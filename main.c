#include <stdio.h>
#include <sys/stat.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <stdint.h>

#define SB_LEN ((1 << 16) - 1)
#define LAB_LEN ((1 << 8) - 1)
#define MIN_MATCH (4)
#define UNCOMPRESSED_BUFFER_LEN (1024 * 1024)
// BIGGEST (LITERALS ONLY) SEQUENCE IS ALWAYS BIGGER THAN A SEQUENCE WITH ANY MATCH
#define LONGEST_LITERAL_SEQUENCE (1 + UNCOMPRESSED_BUFFER_LEN / 255 + 1 + UNCOMPRESSED_BUFFER_LEN + 2)
#define COMPRESSED_BUFFER_LEN (1024 * 1024 + LONGEST_LITERAL_SEQUENCE)

// WE DONT FREE MEMORY BECAUSE ITS SUPPOSED TO END ONCE COMPRESSION OR DECOMPRESSION IS FINISHED
// ALLOCATION IS DETERMINED STATICALLY BOUNDED AND LOW

//TODO: MAKE INTER-ENDIAN COMPATIBLE

typedef struct lzc_in_buffer
{
  size_t forgotten_bytes;
  unsigned char *buffer;
  int32_t buffer_content_len;
  int32_t buffer_size;
  size_t file_size;
  FILE *fp;
} lzc_in_buffer;

lzc_in_buffer *init_lz_in_buffer(FILE* file, size_t file_size, int32_t buffer_size)
{
  lzc_in_buffer *lb = malloc(sizeof(lzc_in_buffer));
  lb->forgotten_bytes = 0;
  lb->buffer = malloc(buffer_size);
  lb->buffer_size = buffer_size;
  lb->buffer_content_len = 0;
  lb->file_size = file_size;
  lb->fp = file;

  return lb;
}

int32_t read_chunk_lz_in_buffer(lzc_in_buffer* lb, int32_t n_bytes_to_preserve)
{
  lb->forgotten_bytes += lb->buffer_content_len - n_bytes_to_preserve;
  memmove(lb->buffer, lb->buffer + (lb->buffer_content_len - n_bytes_to_preserve), n_bytes_to_preserve);
  lb->buffer_content_len = fread(lb->buffer + n_bytes_to_preserve, 1, lb->buffer_size - n_bytes_to_preserve, lb->fp) + n_bytes_to_preserve;

  return lb->buffer_content_len;
}

typedef struct lzc_out_buffer
{
  size_t bytes_written;
  int32_t buffer_content_len;
  unsigned char *buffer;
  size_t buffer_size;
  FILE *fp;
} lzc_out_buffer;

lzc_out_buffer *init_lz_out_buffer(FILE* fp, size_t size)
{
  lzc_out_buffer *lb = malloc(sizeof(lzc_out_buffer));
  lb->buffer_content_len = 0;
  lb->buffer = malloc(size);
  lb->buffer_size = size;
  lb->bytes_written = 0;
  lb->fp = fp;

  return lb;
}

void lz_write_chunk(lzc_out_buffer *lb, int32_t n_bytes_to_preserve)
{
  fwrite(lb->buffer, 1, lb->buffer_content_len - n_bytes_to_preserve, lb->fp);
  memmove(lb->buffer, lb->buffer + (lb->buffer_content_len - n_bytes_to_preserve), n_bytes_to_preserve);
  lb->bytes_written += lb->buffer_content_len - n_bytes_to_preserve;
  lb->buffer_content_len = n_bytes_to_preserve;
}

// tamano de la tabla debe ser 2^p.
uint32_t uk_hash(uint32_t key, uint16_t p)
{
  uint32_t ALPHA = 2654435769; // 2^32 * phi
  return (key * ALPHA) >> (32 - p);
}

typedef struct prefix_table
{
  int32_t *prefixes;
  uint32_t buffer_size;
  uint32_t mask;
  uint32_t max_n;
  uint32_t n;
  uint16_t p;
} prefix_table;

prefix_table *init_prefix_table(size_t size)
{

  uint32_t buffer_size = 2;
  uint16_t p = 1;
  while (buffer_size <= size * 2)
  {
    buffer_size *= 2;
    p++;
  }

  prefix_table *map = malloc(sizeof(prefix_table));
  map->max_n = size;
  map->buffer_size = buffer_size;
  map->prefixes = malloc(buffer_size * sizeof(int32_t));
  map->n = 0;
  map->p = p;

  for (int32_t i = 0; i < buffer_size; i++)
    map->prefixes[i] = -1;
  return map;
}

void prefix_table_push(uint32_t prefix, int32_t data, prefix_table *table)
{
  uint32_t index = uk_hash(prefix, table->p);
  table->prefixes[index] = data;
}

uint32_t prefix_table_get(uint32_t prefix, prefix_table *table)
{
  uint32_t index = uk_hash(prefix, table->p);
  return table->prefixes[index];
}

void push_seq(lzc_out_buffer *lb, unsigned char *literals, int32_t literals_len, uint16_t match_back_offset, int32_t match_len)
{

  if (lb->buffer_content_len + (literals_len / 255 + 1 + match_len / 255 + 1 + 2 + literals_len) >= lb->buffer_size)
  {
    lz_write_chunk(lb, 0);
  }

  int32_t literals_len_cpy = literals_len - 15;
  int32_t match_len_cpy = match_len - 15;
  unsigned char token_high_bits = 0;
  unsigned char token_low_bits = 0;

  if (literals_len < 15)
  {
    token_high_bits = (unsigned char)literals_len;
  }
  else
    token_high_bits = 15;

  if (match_len < 15) // NO bias of (MIN_MATCH)
  {
    token_low_bits = (unsigned char)(match_len);
  }
  else
    token_low_bits = 15;

  lb->buffer[lb->buffer_content_len++] = token_low_bits | (token_high_bits << 4); // asegurarse LOL

  if (literals_len_cpy >= 0)
  {
    while (literals_len_cpy >= 255)
    {
      lb->buffer[lb->buffer_content_len++] = 255;
      literals_len_cpy -= 255;
    }

    lb->buffer[lb->buffer_content_len++] = (unsigned char)literals_len_cpy;
  }

  *(uint16_t *)(lb->buffer + lb->buffer_content_len) = match_back_offset;

  lb->buffer_content_len += 2;

  if (match_len_cpy >= 0)
  {
    while (match_len_cpy >= 255)
    {
      lb->buffer[lb->buffer_content_len++] = 255;
      match_len_cpy -= 255;
    }

    lb->buffer[lb->buffer_content_len++] = (unsigned char)match_len_cpy;
  }

  for (int32_t i = 0; i < literals_len; i++)
  {
    lb->buffer[lb->buffer_content_len++] = literals[i];
  }

}

void insert_key(unsigned char *buffer, int32_t key_offset, int32_t index, prefix_table *ht)
{
  unsigned char *shifted_in = buffer + key_offset;

  int32_t key = *(int32_t *)(shifted_in);
  int32_t data = index;
  prefix_table_push(key, data, ht);
}

int32_t get_possible_prefix_match(unsigned char *lab, prefix_table *ht)
{
  return prefix_table_get(*(uint32_t *)(lab), ht);
}

size_t compress(lzc_in_buffer* lb_in, lzc_out_buffer *lb_out)
{

  prefix_table *ht = init_prefix_table(SB_LEN);
  int32_t relative_possible_match_i = 0;

  int32_t leftover_active_content;
  int32_t match_len = 0;
  int32_t lab_offset = 0; // offset inside the partial buffer.
  int32_t max_len;
  int32_t first_seq_literal = 0;

  unsigned char *limitp;
  unsigned char *basep;
  unsigned char *dicp;
  unsigned char *labp;

  read_chunk_lz_in_buffer(lb_in, 0);

  limitp = lb_in->buffer + lb_in->buffer_content_len - 1;

  while (lab_offset < lb_in->buffer_content_len)
  {

    if (lab_offset + LAB_LEN >= lb_in->buffer_size)
    {
      if (first_seq_literal < lab_offset - SB_LEN)
      {
        push_seq(lb_out, lb_in->buffer + first_seq_literal, (lab_offset - SB_LEN) - first_seq_literal, (uint16_t)0, 0);
        first_seq_literal = 0;
      }
      else
        first_seq_literal -= (lab_offset - SB_LEN);

      leftover_active_content = lb_in->buffer_size - (lab_offset - SB_LEN);
      read_chunk_lz_in_buffer(lb_in, leftover_active_content);
      limitp = lb_in->buffer + lb_in->buffer_content_len - 1;
      lab_offset = SB_LEN;
    }

    relative_possible_match_i = get_possible_prefix_match(lb_in->buffer + lab_offset, ht);

    if (relative_possible_match_i == -1 || (relative_possible_match_i -= lb_in->forgotten_bytes) < (lab_offset - SB_LEN))
    {
      insert_key(lb_in->buffer, lab_offset, lb_in->forgotten_bytes + lab_offset, ht);
      ++lab_offset;
      continue;
    }

    basep = lb_in->buffer + relative_possible_match_i;
    dicp = basep;
    labp = lb_in->buffer + lab_offset;

    while (*(dicp++) == *(labp++) && labp <= limitp);

    match_len = (dicp - basep) - 1;

    if (match_len >= MIN_MATCH)
    {
      push_seq(lb_out, lb_in->buffer + first_seq_literal, lab_offset - first_seq_literal, (uint16_t)(lab_offset - relative_possible_match_i), match_len);
      insert_key(lb_in->buffer, lab_offset, lb_in->forgotten_bytes + lab_offset, ht);

      lab_offset += match_len;
      first_seq_literal = lab_offset;
    }
    else
    {
      insert_key(lb_in->buffer, lab_offset, lb_in->forgotten_bytes + lab_offset, ht);
      ++lab_offset;
    }
  }
  // push sequence if we have buffered literals.
  if (first_seq_literal < lb_in->buffer_content_len)
    push_seq(lb_out, lb_in->buffer + first_seq_literal, lb_in->buffer_content_len - first_seq_literal, 0, 0);

  // flush to disk lz buffer
  lz_write_chunk(lb_out, 0);
  return lb_out->bytes_written;
}

size_t decompress(lzc_in_buffer* lb_in, lzc_out_buffer* lb_out)
{

  int32_t leftover_content = 0;
  int32_t in_i = 0;

  while (lb_in->forgotten_bytes + in_i < lb_in->file_size)
  {

    if (in_i >= (lb_in->buffer_content_len - LONGEST_LITERAL_SEQUENCE) && (lb_in->forgotten_bytes + lb_in->buffer_content_len) < lb_in->file_size)
    {
      leftover_content = lb_in->buffer_content_len - in_i;
      read_chunk_lz_in_buffer(lb_in, leftover_content);
      in_i = 0;
    }

    int32_t copy_start = 0;
    int32_t seq_start = 0;
    int32_t literals_len = 0;
    int32_t match_len = 0;
    uint16_t back_offset = 0;

    seq_start = in_i;

    // LITERALS LEN
    literals_len = (lb_in->buffer[seq_start] & 0b11110000) >> 4;
    ++in_i;
    if (literals_len == 0b00001111) // literals length is multibyte.
      do
      {
        literals_len += lb_in->buffer[in_i];
      } while (lb_in->buffer[in_i++] == 0b11111111);
    // END LITERALS LEN

    // BACK OFFSET
    back_offset = *(uint16_t *)(lb_in->buffer + in_i);
    in_i += 2;
    // END BACK OFFSET

    // MATCH LEN
    match_len = (lb_in->buffer[seq_start] & 0b00001111);

    if (match_len == 0b00001111) // match length is multibyte.
      do
      {
        match_len += lb_in->buffer[in_i];
      } while (lb_in->buffer[in_i++] == 0b11111111);
    // END MATCH LEN.

    // MAKE SURE THERE IS ENOUGH SPACE
    if (lb_out->buffer_content_len + literals_len + match_len >= lb_out->buffer_size) {
      lz_write_chunk(lb_out, SB_LEN);
    }
    // END MAKE SURE THERE ENOUGH SPACE

    // COPY LITERALS
    for (int32_t i = 0; i < literals_len; i++)
      lb_out->buffer[lb_out->buffer_content_len++] = lb_in->buffer[in_i + i]; // Copy literals

    in_i += literals_len;
    // END COPY LITERALS

    // COPY MATCH
    copy_start = lb_out->buffer_content_len - (int32_t)back_offset;

    for (int32_t i = 0; i < match_len; i++)
      lb_out->buffer[lb_out->buffer_content_len++] = lb_out->buffer[copy_start + i]; // Copy match
    // END COPY MATCH
  }

  lz_write_chunk(lb_out, 0);
  return lb_out->bytes_written;
}

int32_t main(int32_t argc, char **argv)
{

  FILE *fp;
  struct stat st_in;
  struct stat st_out;
  char *out_name;

  FILE *fp_out;
  FILE *fp_in;

  if (argc < 3)
  {
    printf("error: not enough parameters.\n");
    return 0;
  }

  if (stat(argv[2], &st_in) == -1)
  {
    printf("error: cannot open file.\n");
    return 0;
  }

  if (strcmp(argv[1], "-d") == 0)
  {

    int32_t original_name_len = strlen(argv[2]);

    if (argc >= 5 && strcmp(argv[3], "-o") == 0)
      out_name = argv[4];
    else if (
        argv[2][original_name_len - 4] == '.' &&
        argv[2][original_name_len - 3] == 'l' &&
        argv[2][original_name_len - 2] == 'z' &&
        argv[2][original_name_len - 1] == 'c')
    {
      out_name = malloc(original_name_len - 4 + 1);
      strncpy(out_name, argv[2], original_name_len - 4);
    }
    else
    {
      out_name = malloc(original_name_len + strlen("_uncompressed") + 1);
      out_name = strcpy(out_name, argv[2]);
      out_name = strcat(out_name, "_uncompressed");
    }

    printf("decompressing %s to %s.\n", argv[2], out_name);

    fp_in = fopen(argv[2], "rwb");
    fp_out = fopen(out_name, "aw");

    if (fp_in == NULL) {
      printf("error: cannot open input file.\n");
      return 0;
    }
    if (fp_out == NULL) {
      printf("error: cannot create output file.\n");
      return 0;
    }

    lzc_out_buffer *out_buff = init_lz_out_buffer(fp_out, UNCOMPRESSED_BUFFER_LEN*2);
    lzc_in_buffer *in_buff = init_lz_in_buffer(fp_in, st_in.st_size, COMPRESSED_BUFFER_LEN);

    printf("Final file size: %li bytes.\n", decompress(in_buff, out_buff));
  }
  else if (strcmp(argv[1], "-c") == 0)
  {

    if (argc > 4 && strcmp(argv[3], "-o") == 0)
      out_name = argv[4];
    else
    {
      out_name = malloc(strlen(argv[2]) + 4 + 1);
      out_name = strcpy(out_name, argv[2]);
      out_name = strcat(out_name, ".lzc");
    }

    fp_in = fopen(argv[2], "rb");
    fp_out = fopen(out_name, "awb");

    if (fp_in == NULL) {
      printf("error: cannot open input file.\n");\
      return 0;
    }
    if (fp_out == NULL) {
      printf("error: cannot create output file.\n");
      return 0;
    }

    printf("compressing %s to %s.\n", argv[2], out_name);
    lzc_out_buffer *out_buff = init_lz_out_buffer(fp_out, COMPRESSED_BUFFER_LEN);
    lzc_in_buffer *in_buff = init_lz_in_buffer(fp_in, st_in.st_size, UNCOMPRESSED_BUFFER_LEN);

    printf("Original file size of %li bytes compressed to %li bytes.\n", st_in.st_size, compress(in_buff, out_buff));
  }
  else
  {
    printf("error: no mode specified.\n");
    return 0;
  }

  return 0;
}
