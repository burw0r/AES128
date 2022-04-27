'''
AES 128 in CBC and ECB mode
Author: Luka Srdarev

AES NIST specification: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.197.pdf
'''
from builtins import enumerate
from typing import List

from utils import *
import os


# -----------------------------------------------------------------------------------------------------

def sub_bytes(s_matrix):
    for r in range(4):
        for c in range(4):
            s_matrix[r][c] = s_box[s_matrix[r][c]]
    return s_matrix


def inv_sub_bytes(s_matrix):
    for r in range(4):
        for c in range(4):
            s_matrix[r][c] = inv_s_box[s_matrix[r][c]]


# -----------------------------------------------------------------------------------------------------

def rotate_arr_left(arr: list, n: int):
    """use negative n to rotate right"""
    return arr[n:] + arr[:n]


def shift_rows(s_matrix):
    for row_index in range(4):
        s_matrix[row_index] = rotate_arr_left(s_matrix[row_index], row_index)
    return s_matrix


def inv_shift_rows(s_matrix):
    for row_index in range(4):
        s_matrix[row_index] = rotate_arr_left(s_matrix[row_index], -row_index)  # -row_index to rotate right
    return s_matrix


# -----------------------------------------------------------------------------------------------------


def add_round_key(s_matrix, round_key: bytes):
    for r in range(4):
        for c in range(4):
            s_matrix[r][c] ^= round_key[r][c]


# -----------------------------------------------------------------------------------------------------


def mix_columns(state):
    for i in range(4):
        s0 = mul_by_02[state[0][i]] ^ mul_by_03[state[1][i]] ^ state[2][i] ^ state[3][i]
        s1 = state[0][i] ^ mul_by_02[state[1][i]] ^ mul_by_03[state[2][i]] ^ state[3][i]
        s2 = state[0][i] ^ state[1][i] ^ mul_by_02[state[2][i]] ^ mul_by_03[state[3][i]]
        s3 = mul_by_03[state[0][i]] ^ state[1][i] ^ state[2][i] ^ mul_by_02[state[3][i]]
        state[0][i] = s0
        state[1][i] = s1
        state[2][i] = s2
        state[3][i] = s3
    return state


def inv_mix_columns(state):
    for i in range(4):
        s0 = mul_by_0e[state[0][i]] ^ mul_by_0b[state[1][i]] ^ mul_by_0d[state[2][i]] ^ mul_by_09[state[3][i]]
        s1 = mul_by_09[state[0][i]] ^ mul_by_0e[state[1][i]] ^ mul_by_0b[state[2][i]] ^ mul_by_0d[state[3][i]]
        s2 = mul_by_0d[state[0][i]] ^ mul_by_09[state[1][i]] ^ mul_by_0e[state[2][i]] ^ mul_by_0b[state[3][i]]
        s3 = mul_by_0b[state[0][i]] ^ mul_by_0d[state[1][i]] ^ mul_by_09[state[2][i]] ^ mul_by_0e[state[3][i]]
        state[0][i] = s0
        state[1][i] = s1
        state[2][i] = s2
        state[3][i] = s3
    return state


# -----------------------------------------------------------------------------------------------------


def in_bytes_to_matrix(bytes_in: bytes):
    s_matrix = []
    index = 0
    for r in range(4):
        row = []
        for c in range(4):
            row.append(bytes_in[index])
            index += 1
        s_matrix.append(row)

    return s_matrix


def matrix_to_output_bytes(state_matrix) -> bytes:
    bytes_out = []
    for r in range(4):
        for c in range(4):
            bytes_out.append(state_matrix[r][c])
    return bytes(bytes_out)


def bytewise_xor(b1: bytes, b2: bytes) -> bytes:
    ret = []
    for index in range(len(b1)):
        ret.append(b1[index] ^ b2[index])
    return bytes(ret)


# -----------------------------------------------------------------------------------------------------
def add_padding(in_bytes: bytes) -> bytes:
    if len(in_bytes) % 16 == 0:
        return in_bytes + (b'\x10' * 16)  # adds another block if len(bytes)%16 == 0
    else:
        add_byte = 16 - (len(in_bytes) % 16)
        return in_bytes + bytes([add_byte] * add_byte)


def remove_padding(in_bytes: bytes) -> bytes:
    pad_length = in_bytes[-1]
    return in_bytes[:-pad_length]


def split_into_blocks(in_bytes: bytes) -> List[bytes]:
    if len(in_bytes) % 16 != 0:
        return ValueError
    else:
        return list([in_bytes[index:index + 16] for index in range(0, len(in_bytes), 16)])


def generate_iv() -> bytes:
    return os.urandom(16)


class AES:

    def __init__(self, master_key):


        (self.Nb, self.Nk, self.Nr) = (4, 4, 10)
        self.master_key = master_key
        print("master key set => ", self.master_key)
        self.state = None
        self.round_keys = self.expand_key()

        ''' 
        Nb = Number of columns comprising the State, Nb = 4
        Nk = Number of 32 bit words comprising the cipher key, for AES128 Nk: 128/32 = 4
        Nr = Number of rounds, function of Nk and Nb,
                for Nb = 4, Nr depends on the Nk like 
                    Nk: Nr
                    4 : 10
                    6 : 12
                    8 : 14

            for AES128 Nr = 10
        '''

    def expand_key(self):
        """
        ref: https://en.wikipedia.org/wiki/AES_key_schedule
             https://wikimedia.org/api/rest_v1/media/math/render/svg/d407710cb9bb9fd9696dc127f6f90c5a95fdaa14
        """

        key_matrix = in_bytes_to_matrix(self.master_key)

        i = 1
        while len(key_matrix) < (self.Nr + 1) * 4:
            word = list(key_matrix[-1])
            if len(key_matrix) % self.Nk == 0:
                word = rotate_arr_left(word, 1)  # ------------- rot word -----------------
                for index in range(len(word)):  # ------------- sub word -----------------
                    word[index] = s_box[word[index]]
                word[0] ^= r_con[i]  # ------------- rcon xor -----------------
                i += 1
            word = bytewise_xor(word, key_matrix[-self.Nk])
            key_matrix.append(word)

        # Group key words in 4x4 byte matrices.
        return [key_matrix[4 * i: 4 * (i + 1)] for i in range(len(key_matrix) // 4)]

    def encrypt_block(self, plaintext):
        self.state = in_bytes_to_matrix(plaintext)

        """---------------------------------------------------------------------------------"""
        add_round_key(self.state, self.round_keys[0])

        """ First Nr-1 rounds"""
        for i in range(1, self.Nr):
            sub_bytes(self.state)
            shift_rows(self.state)
            mix_columns(self.state)
            add_round_key(self.state, self.round_keys[i])

        """ final round """
        sub_bytes(self.state)
        shift_rows(self.state)
        add_round_key(self.state, self.round_keys[-1])
        """---------------------------------------------------------------------------------"""

        return matrix_to_output_bytes(self.state)

    def decrypt_block(self, ciphertext):
        cipher_state = in_bytes_to_matrix(ciphertext)

        """---------------------------------------------------------------------------------"""

        add_round_key(cipher_state, self.round_keys[-1])
        inv_shift_rows(cipher_state)
        inv_sub_bytes(cipher_state)

        for i in range(self.Nr - 1, 0, -1):
            add_round_key(cipher_state, self.round_keys[i])
            inv_mix_columns(cipher_state)
            inv_shift_rows(cipher_state)
            inv_sub_bytes(cipher_state)

        add_round_key(cipher_state, self.round_keys[0])

        """---------------------------------------------------------------------------------"""

        return matrix_to_output_bytes(cipher_state)

    def encrypt_ecb(self, plaintext: bytes) -> bytes:
        plaintext = add_padding(plaintext)
        blocks = split_into_blocks(plaintext)
        ciphertext = bytes()
        for k in blocks:
            ciphertext += self.encrypt_block(k)
        return ciphertext

    def decrypt_ecb(self, ciphertext: bytes) -> bytes:
        blocks = split_into_blocks(ciphertext)
        plaintext = bytes()
        for k in blocks:
            plaintext += self.decrypt_block(k)
        return remove_padding(plaintext)

    def encrypt_cbc(self, plaintext):
        plaintext = add_padding(plaintext)
        blocks = split_into_blocks(plaintext)
        self.iv = generate_iv()

        ciphertext = bytes()
        for i, b in enumerate(blocks):
            if i == 0:
                ciphertext += self.encrypt_block(bytewise_xor(b, self.iv))
            else:
                ciphertext += self.encrypt_block(bytewise_xor(b, ciphertext[-16:]))

        return ciphertext

    def decrypt_cbc(self, ciphertext):
        blocks = split_into_blocks(ciphertext)

        plaintext = bytes()
        for i, b in enumerate(blocks):
            if i == 0:
                plaintext += bytewise_xor(self.decrypt_block(b), self.iv)
            else:
                plaintext += bytewise_xor(self.decrypt_block(b), blocks[i-1])

        plaintext = remove_padding(plaintext)
        return plaintext


if __name__ == '__main__':
    key = b'sixteen byte key'
    plaintext = b'sixteen byte MSG'
    aes = AES(key)

    # -----------------------------------  block encryption test --------------------------------------------------------
    ciphertext = aes.encrypt_block(plaintext)
    decrypted = aes.decrypt_block(ciphertext)
    print("plaintext: ", plaintext)
    print("ciphertext: ", ciphertext)
    print("decrypted: ", decrypted)
    print("\n")

    print(" -- testing block encryption -- ")
    print(plaintext == decrypted)

    # ------------------------------- padding test ----------------------------------------------------------------------
    print(" -- testing padding -- ")
    print(b'asd' == remove_padding(add_padding(b'asd')))
    print(b'ASDKLJASKLDJALSJDALSJKDASLKDJAJKSD' == remove_padding(add_padding(b'ASDKLJASKLDJALSJDALSJKDASLKDJAJKSD')))
    print(b'sixteen byte pad' == remove_padding(add_padding(b'sixteen byte pad')))
    print(b'sixteen byte padsixteen byte pad' == remove_padding(add_padding(b'sixteen byte padsixteen byte pad')))
    print(b'' == remove_padding(add_padding(b'')))

    # -----------------------------------  ecb encryption test -----------------------------------------------------------
    print(" -- testing ecb encrpytion -- ")
    plaintext2 = b'testing encrpytion with an arbitrarily long plaintext'
    ciphertext2 = aes.encrypt_ecb(plaintext2)
    decrypted2 = aes.decrypt_ecb(ciphertext2)
    print(plaintext2 == decrypted2)

    # -----------------------------------  cbc encryption test -----------------------------------------------------------
    print(" -- testing cbc encrpytion -- ")
    plaintext3 = b'testing encrpytion with an arbitrarily long plaintext'
    ciphertext3 = aes.encrypt_cbc(plaintext2)
    decrypted3 = aes.decrypt_cbc(ciphertext3)
    print(plaintext3 == decrypted3)
