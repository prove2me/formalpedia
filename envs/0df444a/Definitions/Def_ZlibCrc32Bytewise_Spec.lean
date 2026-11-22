-- Prove2me | Definitions.Def_ZlibCrc32Bytewise_Spec
-- name    : ZlibCrc32Bytewise_Spec
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T01:53:24.015028+00:00
-- url     : https://prove2.me/theorems/909dae80-db58-4b5e-9d87-b3318130eee9
-- title:
--   Contract of zlib's byte-at-a-time crc32_z on AArch64
-- statement:
--   The table-driven loop of zlib's `crc32_z` and a contract for `crc32_z` in the placed library `zlibCrc32Lib` of the `-DZ_TESTW=` build (bundle `ZlibCrc32Bytewise_PlacedObj`).
--
--   **The loop.**
--   - `tableEntry tbl i` is the little-endian 32-bit word at bytes $4i, \dots, 4i + 3$ of `tbl` (a missing byte counts as $0$).
--   - `crcStep tbl c b` is one step of crc32.c's byte loop (lines 990–1006), `crc = (crc >> 8) ^ crc_table[(crc ^ *buf++) & 0xff]`, with `tbl` in place of `crc_table`: the 32-bit value $c$ shifted right by 8 bits, exclusive-or the table entry at index $(c \oplus b) \bmod 256$.
--   - `crcModel tbl crc bs` is $\lnot\,\mathrm{fold}$ of `crcStep tbl` over the bytes `bs`, started from $\lnot\,\mathit{crc}$ (bitwise complement on 32 bits): the pre-conditioning of line 704, the byte loop and the post-conditioning of line 1009.
--
--   **The contract `crc32zSpec`**, for `crc32_z(crc, buf, len)` with a non-null buffer. Arguments follow AAPCS64: `crc` in `x0`, `buf` in `x1`, `len` in `x2`, the result in `x0`. The ghost value is the byte list `bs` at `buf`.
--   - Precondition: `buf` $\ne 0$, `len` $= |bs|$ (all 64 bits of `x2`), the bytes `bs` readable at `buf` (read-only points-to), and the library's data objects in their initial state (`dataInit`).
--   - Postcondition: `x0` is `crcModel` with the library's own `crc_table` bytes (`zlibCrc32PlacedData0`) as the table and the low 32 bits of the entry `crc`, zero-extended to 64 bits; the buffer and the data objects are handed back unchanged.
--
--   The contract does not say that the result is the CRC-32 of `bs` as a polynomial: it says the machine code computes zlib's table loop over the table bytes the object carries. That those bytes are the CRC-32 table is a separate claim (for the default build, the milestone `ZlibCrc32.crc_tables_eq` of the mission "zlib 1.3.1 CRC-32 on AArch64"). The `buf = Z_NULL` case is not covered.
-- source:
--   zlib 1.3.1 (J.-l. Gailly and M. Adler, January 22, 2024; https://zlib.net/fossils/zlib-1.3.1.tar.gz, SHA-256 9a93b2b7dfdac77ceba5a558a580e74667dd6fede4585b91eefb60f03b72df23), crc32.c lines 694–1010 (crc32_z): the pre-conditioning at line 704, the byte loop at lines 990–1006 and the post-conditioning at line 1009

module

public import Definitions.Def_Arm64_Spec_Placed
public import Definitions.Def_ZlibCrc32Bytewise_PlacedObj

/-! # Contract of zlib 1.3.1 `crc32_z`, byte-at-a-time build, AArch64

The table-driven loop of zlib's `crc32_z` (`crcModel`) and the contract `crc32zSpec` of the
function `crc32_z` of the placed library `zlibCrc32Lib` (bundle
`Def_ZlibCrc32Bytewise_PlacedObj`) with a non-null buffer.
-/

@[expose] public section

namespace ZlibCrc32Bytewise

open Arm64

/-- Entry `i` of a table of little-endian 32-bit words stored in `tbl`. -/
def tableEntry (tbl : List (BitVec 8)) (i : Nat) : BitVec 32 :=
  (tbl.getD (4 * i + 3) 0#8) ++ (tbl.getD (4 * i + 2) 0#8) ++
    (tbl.getD (4 * i + 1) 0#8) ++ (tbl.getD (4 * i) 0#8)

/-- One step of zlib's byte loop: `crc = (crc >> 8) ^ crc_table[(crc ^ b) & 0xff]`. -/
def crcStep (tbl : List (BitVec 8)) (c : BitVec 32) (b : BitVec 8) : BitVec 32 :=
  (c >>> 8) ^^^ tableEntry tbl ((c ^^^ b.zeroExtend 32).toNat % 256)

/-- zlib's `crc32_z(crc, buf, len)` for non-null `buf`, as a function of the low 32 bits of
    `crc` and the bytes `bs` at `buf`: pre-condition, byte loop, post-condition. -/
def crcModel (tbl : List (BitVec 8)) (crc : BitVec 32) (bs : List (BitVec 8)) : BitVec 32 :=
  ~~~ (bs.foldl (crcStep tbl) (~~~ crc))

/-- Contract of `crc32_z` with a non-null buffer: entered with `x0 = crc`, `x1 = buf ≠ 0`,
    `x2 = len = bs.length`, `buf ↦ᵣ bs` and the library's data (the CRC table) in place, it
    returns with `x0` the zero-extended `crcModel`, the buffer and the data unchanged. -/
def crc32zSpec (pl : Obj.Placement) : Spec (List (BitVec 8)) where
  pre bs s0 :=
    ⌜s0.readReg64 Reg.x1 ≠ 0#64 ∧ (s0.readReg64 Reg.x2).toNat = bs.length⌝ ∗
      (s0.readReg64 Reg.x1 ↦ᵣ bs) ∗ zlibCrc32Lib.dataInit pl
  post bs s0 sf :=
    ⌜sf.readReg64 Reg.x0 =
        (crcModel zlibCrc32PlacedData0 ((s0.readReg64 Reg.x0).truncate 32) bs).zeroExtend 64⌝ ∗
      (s0.readReg64 Reg.x1 ↦ᵣ bs) ∗ zlibCrc32Lib.dataInit pl

end ZlibCrc32Bytewise


