-- Prove2me | Definitions.Def_ZlibCrc32_Spec
-- name    : ZlibCrc32_Spec
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T01:31:22.699607+00:00
-- url     : https://prove2.me/theorems/4f3059e4-38db-449d-a3f0-9e7e3acef33b
-- title:
--   Contracts of zlib's CRC-32 functions on AArch64
-- statement:
--   The CRC-32 as a polynomial, and one contract per exported function of `zlibCrc32Lib`. A statement `zlibCrc32Lib.subroutineOk "f" spec` (from the `Arm64` bundles) is total correctness of `f` under `spec` for every valid placement of the library. For every frame $R$ and every entry state at `f` with a 16-byte-aligned stack pointer whose memory satisfies the precondition separately from $R$, execution terminates. It returns to the link register with the stack pointer and the AAPCS64 callee-saved registers restored, and the memory satisfies the postcondition, again with $R$ separate. Panics, process exits and running out of memory are excluded.
--
--   **CRC-32.** The polynomial objects are Kadatch–Jenkins' (bundle `KadatchJenkinsCrc`).
--   - `crc32P` is the CRC-32 polynomial $P(x) = x^{32} + x^{26} + x^{23} + x^{22} + x^{16} + x^{12} + x^{11} + x^{10} + x^8 + x^7 + x^5 + x^4 + x^2 + x + 1$. Its coefficients below $x^{32}$ are `0x04C11DB7`, and crc32.c's `POLY` `0xedb88320` is the same bits reflected (crc32.c, line 149: “p(x) reflected, with x^32 implied”).
--   - `crc32Poly c bs` is $\mathrm{CRC}_u(M, v)$ of eq. (1) with this $P$ and $u = x^{31} + \dots + x + 1$ (eq. (2)). Here $M$ is the message of the bytes `bs`: bit $i$ of byte $j$ (bit 0 least significant) is message bit $8j + i$ (`Message.ofBytes`). $v$ is the polynomial of the 32-bit value `c`: bit $i$ is the coefficient of $x^{31-i}$ (`regPoly`, §4.1).
--   - `Holds32 r p` says that the 64-bit register value `r` is below $2^{32}$ and the polynomial of its low 32 bits is `p`.
--   - `word32 tbl i` is the little-endian 32-bit word at bytes $4i, \dots, 4i + 3$ of `tbl`.
--
--   **The functions, in zlib.h's words.**
--   - `crc32` (lines 1732–1736): “Update a running CRC-32 with the bytes buf[0..len-1] and return the updated CRC-32. A CRC-32 value is in the range of a 32-bit unsigned integer. If buf is Z_NULL, this function returns the required initial value for the crc. Pre- and post-conditioning (one's complement) is performed within this function so it shouldn't be done by the application.”
--   - `crc32_z` (line 1751): “Same as crc32(), but with a size_t length.”
--   - `crc32_combine` (lines 1757–1761): “Combine two CRC-32 check values into one. For two sequences of bytes, seq1 and seq2 with lengths len1 and len2, CRC-32 check values were calculated for each, crc1 and crc2. crc32_combine() returns the CRC-32 check value of seq1 and seq2 concatenated, requiring only crc1, crc2, and len2. len2 must be non-negative.”
--   - `crc32_combine_gen` (lines 1767–1768): “Return the operator corresponding to length len2, to be used with crc32_combine_op(). len2 must be non-negative.”
--   - `crc32_combine_op` (lines 1773–1775): “Give the same result as crc32_combine(), using op in place of len2. op is is generated from len2 by crc32_combine_gen(). This will be faster than crc32_combine() if the generated op is used more than once.”
--   - `get_crc_table` (line 1916) is listed among the “undocumented functions”.
--
--   **The contracts.** Arguments are in `x0`, `x1`, `x2` and the result is in `x0` (AAPCS64). Each contract lends the library's data objects in their initial state (`dataInit`) and returns them unchanged.
--   - `crc32zSpec`, for `crc32_z(crc, buf, len)`. The ghost value is `none` for `buf = 0` and `some bs` for a buffer.
--     - With `none` the result is $0$.
--     - With `some bs`, the bytes `bs` are readable at `buf` (read-only points-to), `len` $= |bs|$, and the result satisfies `Holds32` with `crc32Poly (crc mod 2^32) bs`. The buffer is returned.
--     - Both cases lend the 96 bytes below the stack pointer, with any contents, and get them back.
--   - `crc32Spec`, for `crc32`: the same, with `len` read from the low 32 bits of `x2`.
--   - `crc32CombineSpec`, for `crc32_combine` and `crc32_combine64`. The ghost value is a pair of byte strings $(A, B)$, with:
--     - the low 32 bits of `crc1` having polynomial `crc32Poly 0 A`;
--     - the low 32 bits of `crc2` having polynomial `crc32Poly 0 B`;
--     - `len2`, read as a signed integer, equal to $|B|$.
--
--     The result satisfies `Holds32` with `crc32Poly 0 (A ++ B)`.
--   - `crc32CombineGenSpec`, for `crc32_combine_gen` and `crc32_combine_gen64`: if `len2`, read as a signed integer, is $n \ge 0$, the result satisfies `Holds32` with $x^{8n} \bmod P$.
--   - `crc32CombineOpSpec`, for `crc32_combine_op`: as `crc32CombineSpec`, with the low 32 bits of `op` having polynomial $x^{8|B|} \bmod P$ in place of the hypothesis on `len2`.
--   - `getCrcTableSpec`, for `get_crc_table`: the result is the address of `crc_table` and points to 1024 readable bytes whose word $i$ ($i < 256$) has polynomial $\mathrm{CRC}_0$ of the one-byte message $i$ from $0$ (eq. (7)).
--
--   The readings of zlib.h's sentences are explained in each statement's note.
-- source:
--   zlib 1.3.1 (J.-l. Gailly and M. Adler, January 22, 2024; https://zlib.net/fossils/zlib-1.3.1.tar.gz, SHA-256 9a93b2b7dfdac77ceba5a558a580e74667dd6fede4585b91eefb60f03b72df23), zlib.h lines 1730–1776 (crc32, crc32_z, crc32_combine, crc32_combine_gen, crc32_combine_op) and 1916 (get_crc_table)

import Definitions.Def_KadatchJenkinsCrc
import Definitions.Def_ZlibCrc32_PlacedObj
import Definitions.Def_Arm64_Spec_Placed

/-!
# Contracts of zlib 1.3.1's CRC-32 functions on AArch64

The CRC-32 of a byte string as a polynomial over `GF(2)` (Kadatch–Jenkins' `CRC_u` with the
CRC-32 parameters), the 32-bit words of zlib's tables, and one contract (`Arm64.Spec`) for each
exported function of the placed library `zlibCrc32Lib`.

Registers follow AAPCS64: arguments in `x0`, `x1`, `x2`, the result in `x0`. A 32-bit value is
read from the low 32 bits of its register.
-/

open Polynomial Arm64 KadatchJenkins

namespace ZlibCrc32

/-- The CRC-32 generator polynomial
`x^32 + x^26 + x^23 + x^22 + x^16 + x^12 + x^11 + x^10 + x^8 + x^7 + x^5 + x^4 + x^2 + x + 1`
(`0x04C11DB7` with the leading `x^32`). -/
noncomputable def crc32P : (ZMod 2)[X] :=
  X ^ 32 + X ^ 26 + X ^ 23 + X ^ 22 + X ^ 16 + X ^ 12 + X ^ 11 + X ^ 10 + X ^ 8 + X ^ 7 +
    X ^ 5 + X ^ 4 + X ^ 2 + X + 1

/-- The CRC-32 of the bytes `bs` continued from the running CRC-32 value `c`, as a polynomial:
`CRC_u(M, v)` with `P = crc32P`, `u = x^31 + ⋯ + 1`, `M` the message of `bs` and `v` the
polynomial of the register value `c`. -/
noncomputable def crc32Poly (c : BitVec 32) (bs : List (BitVec 8)) : (ZMod 2)[X] :=
  crc crc32P (stdU 32) (Message.ofBytes bs) (regPoly c)

/-- The 64-bit register value `r` holds a 32-bit value (upper half zero) whose polynomial is `p`. -/
def Holds32 (r : BitVec 64) (p : (ZMod 2)[X]) : Prop :=
  r.toNat < 2 ^ 32 ∧ regPoly (r.setWidth 32) = p

/-- Entry `i` of a table of little-endian 32-bit words stored in the bytes `tbl`. -/
def word32 (tbl : List (BitVec 8)) (i : ℕ) : BitVec 32 :=
  (tbl.getD (4 * i + 3) 0#8) ++ (tbl.getD (4 * i + 2) 0#8) ++
    (tbl.getD (4 * i + 1) 0#8) ++ (tbl.getD (4 * i) 0#8)

/-- Contract of `crc32_z(crc, buf, len)` (`x0 = crc`, `x1 = buf`, `x2 = len`). The ghost value is
`none` for `buf = Z_NULL` and `some bs` for a buffer holding the bytes `bs`. The caller provides a
96-byte stack frame below `sp` and the library's tables; both, and the buffer, are handed back.
- `buf = Z_NULL` (`x1 = 0`), any `crc` and `len`: the result is `0`.
- `buf ≠ Z_NULL` holding `bs` (readable), `len = |bs|`: the result is the 32-bit value whose
  polynomial is `crc32Poly (crc mod 2^32) bs`. -/
def crc32zSpec (pl : Obj.Placement) : Arm64.Spec (Option (List (BitVec 8))) where
  pre g s0 :=
    match g with
    | none =>
      ⌜s0.readReg64 Reg.x1 = 0#64⌝ ∗ stackFrame s0 96 ∗ zlibCrc32Lib.dataInit pl
    | some bs =>
      ⌜s0.readReg64 Reg.x1 ≠ 0#64 ∧ (s0.readReg64 Reg.x2).toNat = bs.length⌝ ∗
        (s0.readReg64 Reg.x1 ↦ᵣ bs) ∗ stackFrame s0 96 ∗ zlibCrc32Lib.dataInit pl
  post g s0 sf :=
    match g with
    | none =>
      ⌜sf.readReg64 Reg.x0 = 0#64⌝ ∗ stackFrame s0 96 ∗ zlibCrc32Lib.dataInit pl
    | some bs =>
      ⌜Holds32 (sf.readReg64 Reg.x0) (crc32Poly ((s0.readReg64 Reg.x0).setWidth 32) bs)⌝ ∗
        (s0.readReg64 Reg.x1 ↦ᵣ bs) ∗ stackFrame s0 96 ∗ zlibCrc32Lib.dataInit pl

/-- Contract of `crc32(crc, buf, len)` with a 32-bit `len` (`uInt`): as `crc32zSpec`, with the
length read from the low 32 bits of `x2`. -/
def crc32Spec (pl : Obj.Placement) : Arm64.Spec (Option (List (BitVec 8))) where
  pre g s0 :=
    match g with
    | none =>
      ⌜s0.readReg64 Reg.x1 = 0#64⌝ ∗ stackFrame s0 96 ∗ zlibCrc32Lib.dataInit pl
    | some bs =>
      ⌜s0.readReg64 Reg.x1 ≠ 0#64 ∧ ((s0.readReg64 Reg.x2).setWidth 32).toNat = bs.length⌝ ∗
        (s0.readReg64 Reg.x1 ↦ᵣ bs) ∗ stackFrame s0 96 ∗ zlibCrc32Lib.dataInit pl
  post g s0 sf :=
    match g with
    | none =>
      ⌜sf.readReg64 Reg.x0 = 0#64⌝ ∗ stackFrame s0 96 ∗ zlibCrc32Lib.dataInit pl
    | some bs =>
      ⌜Holds32 (sf.readReg64 Reg.x0) (crc32Poly ((s0.readReg64 Reg.x0).setWidth 32) bs)⌝ ∗
        (s0.readReg64 Reg.x1 ↦ᵣ bs) ∗ stackFrame s0 96 ∗ zlibCrc32Lib.dataInit pl

/-- Contract of `crc32_combine(crc1, crc2, len2)` and `crc32_combine64` (`x0 = crc1`,
`x1 = crc2`, `x2 = len2` as a signed 64-bit integer). The ghost value is the pair of byte
strings `(A, B)`: the low 32 bits of `crc1` and `crc2` are the CRC-32s of `A` and `B` (from the
initial value `0`), and `len2 = |B|`, which is non-negative. The result is the CRC-32 of `A ++ B`. -/
def crc32CombineSpec (pl : Obj.Placement) : Arm64.Spec (List (BitVec 8) × List (BitVec 8)) where
  pre g s0 :=
    ⌜regPoly ((s0.readReg64 Reg.x0).setWidth 32) = crc32Poly 0#32 g.1 ∧
      regPoly ((s0.readReg64 Reg.x1).setWidth 32) = crc32Poly 0#32 g.2 ∧
      (s0.readReg64 Reg.x2).toInt = (g.2.length : ℤ)⌝ ∗ zlibCrc32Lib.dataInit pl
  post g _ sf :=
    ⌜Holds32 (sf.readReg64 Reg.x0) (crc32Poly 0#32 (g.1 ++ g.2))⌝ ∗ zlibCrc32Lib.dataInit pl

/-- Contract of `crc32_combine_gen(len2)` and `crc32_combine_gen64` (`x0 = len2` as a signed
64-bit integer, ghost `n = len2 ≥ 0`): the result is the 32-bit value whose polynomial is
`x^(8n) mod P`, the operator for appending `n` bytes. -/
def crc32CombineGenSpec (pl : Obj.Placement) : Arm64.Spec ℕ where
  pre n s0 := ⌜(s0.readReg64 Reg.x0).toInt = (n : ℤ)⌝ ∗ zlibCrc32Lib.dataInit pl
  post n _ sf := ⌜Holds32 (sf.readReg64 Reg.x0) (X ^ (8 * n) % crc32P)⌝ ∗ zlibCrc32Lib.dataInit pl

/-- Contract of `crc32_combine_op(crc1, crc2, op)` (`x0 = crc1`, `x1 = crc2`, `x2 = op`): with
`crc1`, `crc2` as in `crc32CombineSpec` and the low 32 bits of `op` the operator
`x^(8|B|) mod P` that `crc32_combine_gen(|B|)` returns, the result is the CRC-32 of `A ++ B`. -/
def crc32CombineOpSpec (pl : Obj.Placement) : Arm64.Spec (List (BitVec 8) × List (BitVec 8)) where
  pre g s0 :=
    ⌜regPoly ((s0.readReg64 Reg.x0).setWidth 32) = crc32Poly 0#32 g.1 ∧
      regPoly ((s0.readReg64 Reg.x1).setWidth 32) = crc32Poly 0#32 g.2 ∧
      regPoly ((s0.readReg64 Reg.x2).setWidth 32) = X ^ (8 * g.2.length) % crc32P⌝ ∗
      zlibCrc32Lib.dataInit pl
  post g _ sf :=
    ⌜Holds32 (sf.readReg64 Reg.x0) (crc32Poly 0#32 (g.1 ++ g.2))⌝ ∗ zlibCrc32Lib.dataInit pl

/-- Contract of `get_crc_table()`: it returns the address of the library's `crc_table`, where
1024 readable bytes hold 256 little-endian 32-bit words, entry `i` being the CRC₀ of the single
byte `i` from `0` (the polynomial of byte `i` times `x^32`, mod `P`); the library's data is
unchanged. -/
def getCrcTableSpec (pl : Obj.Placement) : Arm64.Spec where
  pre _ _ := zlibCrc32Lib.dataInit pl
  post _ _ sf :=
    ⌜sf.readReg64 Reg.x0 = pl.ρ "crc_table [zlib_crc32]"⌝ ∗ (∃∗ tbl : List (BitVec 8),
      ⌜tbl.length = 1024 ∧ ∀ i < 256,
        regPoly (word32 tbl i) = crc0 crc32P (Message.ofBytes [BitVec.ofNat 8 i]) 0⌝ ∗
      (sf.readReg64 Reg.x0 ↦ᵣ tbl)) ∗ zlibCrc32Lib.dataInit pl

end ZlibCrc32


