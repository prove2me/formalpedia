-- Prove2me | Definitions.Def_Musl_StringContracts
-- name    : Musl_StringContracts
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-24T16:41:50.169907+00:00
-- url     : https://prove2.me/theorems/4b28d09e-5ccb-41a1-b590-5b238c1e188c
-- title:
--   Contracts of musl 1.2.5's AArch64 memcpy, memset, memmove, memcmp, bcmp, memchr, memrchr, memccpy, mempcpy, memmem
-- statement:
--   DeepMind's specification of the `src/string/` memory functions of stock musl 1.2.5 on AArch64, from the module [VerifiedLibraries/Musl/Spec/Top.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/VerifiedLibraries/Musl/Spec/Top.lean) of google-deepmind/code-verification (Apache License 2.0), in the namespace `VerifiedLibraries.Musl` with names unchanged. For each function it gives a byte-level reference model (for example `memcmpModel`, `memchrModel`, `memmemModel`) and a contract (`memcpySpec`, `memsetSpec`, `memmoveSpec`, `memcmpSpec`, `bcmpSpec`, `memchrSpec`, `memrchrSpec`, `memccpySpec`, `mempcpySpec`, `memmemSpec`, with read-only-source variants such as `memcmpROSpec`): the arguments in `x0`–`x3`, the memory the function owns, and what it returns in `x0` and leaves in memory.
--
--   Upstream writes each contract with the `c_type_spec` command, which prove2.me does not accept. Here each is written out as the `Spec` term the command elaborates to, as printed by Lean from the upstream module. After elaboration, all 42 constants of the namespace (the contracts, the models and their auxiliary match functions) were compared with those of the upstream module, elaborated with the real command: every type and value is identical. The upstream abbreviation `muslStringProg` and the statement `MuslStringImageOkStmt` are left out, because they refer to the compiled musl object, which is not part of this bundle. The "MODIFIED for prove2.me" notice after the license header lists these changes.
-- source:
--   Google DeepMind, code-verification (arm64-semantics), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module VerifiedLibraries/Musl/Spec/Top.lean (musl 1.2.5 string functions), contracts written out as the terms c_type_spec elaborates to, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/VerifiedLibraries/Musl/Spec/Top.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `VerifiedLibraries/Musl/Spec/Top.lean`,
google-deepmind/code-verification commit 8c8d371f): each `c_type_spec` contract is written out as the
`Spec` term it elaborates to (prove2.me rejects the `c_type_spec` command), printed by Lean from the
upstream module; the abbreviation `muslStringProg` and the statement `MuslStringImageOkStmt`, which refer
to the compiled musl object, are omitted, with the object import; `import Arm64` becomes the published
bundles `Definitions.Def_Arm64` and `Definitions.Def_Arm64_Surface_CType`. The module docstring loses its
clause on `MuslStringImageOkStmt`; other docstrings and every other definition are unchanged.
-/

module

public import Definitions.Def_Arm64
public import Definitions.Def_Arm64_Surface_CType

/-!
# Stock `musl` v1.2.5 AArch64 Memory Primitives Specification

Public specification surface of stock `musl` v1.2.5 AArch64 `src/string/` memory primitives
(`memcpy`, `memset`, `memmove`, `memcmp`, `bcmp`, `memchr`, `memrchr`, `__memrchr`, `memccpy`,
`mempcpy`, and `memmem`) from the Rust `1.98.1` `aarch64-unknown-linux-musl` sysroot (`libc.a`,
SHA-256 `b03473b6f1efb72f700f561b4407a88885b37e0edb5cdb2a64de0df5499e813f`). Defines pure
byte-level reference models, `c_type_spec` contracts (with both mutable/shared and read-only slice
variants).
-/

@[expose] public section

namespace VerifiedLibraries.Musl

open Arm64 Arm64.CType

/-! ## Program and Semantic Types -/

/-- Read-only byte slice `p ↦ᵣ bs` (e.g. `.rodata` constants; pair with `SliceLen bs` for length). -/
@[reducible] def RoSlice8 : SemType (List (BitVec 8)) :=
  { tyName := "const uint8_t[] (read-only)",
    interp := fun p bs => p ↦ᵣ bs,
    pureWf := fun _ _ => True }

/-- Length register coupled to a pair of equal-length byte-slice models `bs1`, `bs2`:
    `n.toNat = bs1.length ∧ n.toNat = bs2.length`. -/
@[reducible] def SliceLenPair (bs1 bs2 : List (BitVec 8)) : SemType (BitVec 64) :=
  { tyName := "size_t (paired slice length)",
    interp := fun _ _ => emp,
    pureWf := fun _ n => n.toNat = bs1.length ∧ n.toNat = bs2.length }

/-- Partially initialized buffer of total capacity `cap` bytes whose prefix holds `bs`
    (`bs.length ≤ cap`) and whose suffix `[p + bs.length, p + cap)` remains uninitialized `memRegion`. -/
@[reducible] def PrefixBuf (cap : Nat) : SemType (List (BitVec 8)) :=
  { tyName := "void * (prefix-initialized buffer)",
    interp := fun p bs =>
      (p ↦ₛ bs) ∗ memRegion (p + BitVec.ofNat 64 bs.length) (cap - bs.length),
    pureWf := fun _ bs => bs.length ≤ cap }

/-! ## Pure Byte-Level Reference Models -/

/-- Result of copying `len` bytes from offset `src` to offset `dst` within a single buffer `buf`. -/
def moveBytes (buf : List (BitVec 8)) (dst src len : Nat) : List (BitVec 8) :=
  buf.take dst ++ (buf.drop src).take len ++ buf.drop (dst + len)

/-- Exact return value of musl's `memcmp(s1, s2, n)` / `bcmp(s1, s2, n)` on two byte slices
    `bs1` and `bs2`: returns `(b1.zeroExtend 32 - b2.zeroExtend 32)` at the first differing
    byte pair `(b1, b2)`, or `0#32` if all compared bytes match. -/
def memcmpBytes : List (BitVec 8) → List (BitVec 8) → BitVec 32
  | b1 :: rest1, b2 :: rest2 =>
    if b1 = b2 then memcmpBytes rest1 rest2
    else b1.zeroExtend 32 - b2.zeroExtend 32
  | _, _ => 0#32

/-- Return value of `memchr(s, c, n)` where `s` holds `bs` (`n = bs.length`):
    `s + i` at the first index `i` where `bs[i] = c`, or `0` (`NULL`) if `c ∉ bs`. -/
def memchrRet (s : BitVec 64) (bs : List (BitVec 8)) (c : BitVec 8) : BitVec 64 :=
  match bs.idxOf? c with
  | some i => s + BitVec.ofNat 64 i
  | none => 0#64

/-- Return value of `memrchr(s, c, n)` / `__memrchr(s, c, n)` where `s` holds `bs` (`n = bs.length`):
    `s + i` at the last index `i` where `bs[i] = c`, or `0` (`NULL`) if `c ∉ bs`. -/
def memrchrRet (s : BitVec 64) (bs : List (BitVec 8)) (c : BitVec 8) : BitVec 64 :=
  match bs.reverse.idxOf? c with
  | some j => s + BitVec.ofNat 64 (bs.length - 1 - j)
  | none => 0#64

/-- Number of bytes copied by `memccpy(dst, src, c, n)` where `src` holds `bs` (`n = bs.length`):
    `k + 1` if `c` first occurs at index `k`, or `bs.length` if `c ∉ bs`. -/
def memccpyCount (bs : List (BitVec 8)) (c : BitVec 8) : Nat :=
  match bs.idxOf? c with
  | some k => k + 1
  | none => bs.length

/-- Return value of `memccpy(dst, src, c, n)` where `src` holds `bs` (`n = bs.length`):
    `dst + (k + 1)` if `c` first occurs at index `k`, or `0` (`NULL`) if `c ∉ bs`. -/
def memccpyRet (dst : BitVec 64) (bs : List (BitVec 8)) (c : BitVec 8) : BitVec 64 :=
  match bs.idxOf? c with
  | some k => dst + BitVec.ofNat 64 (k + 1)
  | none => 0#64

/-- First starting index `i ≤ hs.length - ne.length` where `(hs.drop i).take ne.length = ne`,
    or `none` if `ne` does not occur as a contiguous subslice of `hs`. -/
def memmemIdx? (hs ne : List (BitVec 8)) : Option Nat :=
  if hs.length < ne.length then none
  else (List.range (hs.length - ne.length + 1)).find? fun i =>
    decide ((hs.drop i).take ne.length = ne)

/-- Return value of `memmem(hs, k, ne, l)`: `hs + i` at the first index `i` where `ne` occurs
    in `hs`, or `0` (`NULL`) if `ne` does not occur in `hs`. When `ne = []`, returns `hs`. -/
def memmemRet (hs : BitVec 64) (bsHay bsNee : List (BitVec 8)) : BitVec 64 :=
  match memmemIdx? bsHay bsNee with
  | some i => hs + BitVec.ofNat 64 i
  | none => 0#64

/-! ## Public `c_type_spec` Contracts -/

/-- `memcpy(dst, src, n)` from a mutable/shared byte slice `src ↦ₛ bs`: copies `n = bs.length`
    bytes to disjoint uninitialized buffer `dst` and returns `dst`. -/
def memcpySpec : Arm64.Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8)) :=
{
  pre := fun x s0 =>
    match x with
    | (dst, src, n, bs) =>
      ⌜Arm64.State.readReg64 s0 Arm64.Reg.x0 = dst ∧
            Arm64.State.readReg64 s0 Arm64.Reg.x1 = src ∧
              Arm64.State.readReg64 s0 Arm64.Reg.x2 = n ∧
                Arm64.CType.SemType.pureWf Arm64.CType.ShrSlice8 src bs ∧
                  Arm64.CType.SemType.valWf (Arm64.CType.SliceLen bs) n⌝ ∗
        Arm64.memRegion dst (List.length bs) ∗ Arm64.CType.SemType.interp Arm64.CType.ShrSlice8 src bs,
  post := fun x s0 sf =>
    match x with
    | (dst, src, n, bs) =>
      ⌜Arm64.CType.SemType.pureWf Arm64.CType.MutSlice8 dst bs ∧ Arm64.State.readReg64 sf Arm64.Reg.x0 = dst⌝ ∗
        Arm64.CType.SemType.interp Arm64.CType.MutSlice8 dst bs ∗
          Arm64.CType.SemType.interp Arm64.CType.ShrSlice8 src bs }

/-- `memcpy(dst, src, n)` from a read-only byte slice `src ↦ᵣ bs` (e.g., `.rodata`):
    copies `n = bs.length` bytes to disjoint uninitialized buffer `dst` and returns `dst`. -/
def memcpyROSpec : Arm64.Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8)) :=
{
  pre := fun x s0 =>
    match x with
    | (dst, src, n, bs) =>
      ⌜Arm64.State.readReg64 s0 Arm64.Reg.x0 = dst ∧
            Arm64.State.readReg64 s0 Arm64.Reg.x1 = src ∧
              Arm64.State.readReg64 s0 Arm64.Reg.x2 = n ∧
                Arm64.CType.SemType.pureWf VerifiedLibraries.Musl.RoSlice8 src bs ∧
                  Arm64.CType.SemType.valWf (Arm64.CType.SliceLen bs) n⌝ ∗
        Arm64.memRegion dst (List.length bs) ∗ Arm64.CType.SemType.interp VerifiedLibraries.Musl.RoSlice8 src bs,
  post := fun x s0 sf =>
    match x with
    | (dst, src, n, bs) =>
      ⌜Arm64.CType.SemType.pureWf Arm64.CType.MutSlice8 dst bs ∧ Arm64.State.readReg64 sf Arm64.Reg.x0 = dst⌝ ∗
        Arm64.CType.SemType.interp Arm64.CType.MutSlice8 dst bs ∗
          Arm64.CType.SemType.interp VerifiedLibraries.Musl.RoSlice8 src bs }

/-- `memmove(dst, src, n)`: copies `n` bytes from `src = base + o` to `dst = base + d` within
    a single mutable buffer `base ↦ₛ buf` (`d + n ≤ buf.length ∧ o + n ≤ buf.length`), handling
    arbitrary overlap, and returns `dst`. -/
def memmoveSpec : Arm64.Spec
  (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × Nat × Nat) :=
{
  pre := fun x s0 =>
    match x with
    | (dst, src, n, base, buf, d, o) =>
      ⌜Arm64.State.readReg64 s0 Arm64.Reg.x0 = dst ∧
            Arm64.State.readReg64 s0 Arm64.Reg.x1 = src ∧
              Arm64.State.readReg64 s0 Arm64.Reg.x2 = n ∧
                Arm64.CType.SemType.pureWf (Arm64.CType.InteriorPtr "void *") dst (base + BitVec.ofNat 64 d) ∧
                  Arm64.CType.SemType.pureWf (Arm64.CType.InteriorPtr "const void *") src (base + BitVec.ofNat 64 o) ∧
                    Arm64.CType.SemType.valWf Arm64.CType.SizeT n ∧
                      d + BitVec.toNat n ≤ List.length buf ∧
                        o + BitVec.toNat n ≤ List.length buf ∧
                          BitVec.toNat base + List.length buf ≤ 2 ^ 64 ∧ List.length buf < 2 ^ 63⌝ ∗
        Arm64.CType.SemType.interp (Arm64.CType.InteriorPtr "void *") dst (base + BitVec.ofNat 64 d) ∗
          Arm64.CType.SemType.interp (Arm64.CType.InteriorPtr "const void *") src (base + BitVec.ofNat 64 o) ∗
            base ↦ₛ buf,
  post := fun x s0 sf =>
    match x with
    | (dst, src, n, base, buf, d, o) =>
      ⌜Arm64.State.readReg64 sf Arm64.Reg.x0 = dst⌝ ∗
        Arm64.CType.SemType.interp (Arm64.CType.InteriorPtr "void *") dst (base + BitVec.ofNat 64 d) ∗
          Arm64.CType.SemType.interp (Arm64.CType.InteriorPtr "const void *") src (base + BitVec.ofNat 64 o) ∗
            base ↦ₛ VerifiedLibraries.Musl.moveBytes buf d o (BitVec.toNat n) }

/-- `memset(dst, c, n)`: fills `n` bytes at `dst` with the low 8 bits of `c` and returns `dst`. -/
def memsetSpec : Arm64.Spec (BitVec 64 × BitVec 32 × BitVec 64) :=
{
  pre := fun x s0 =>
    match x with
    | (dst, c, n) =>
      ⌜Arm64.State.readReg64 s0 Arm64.Reg.x0 = dst ∧
            Arm64.State.readReg32 s0 Arm64.Reg.x1 = c ∧
              Arm64.State.readReg64 s0 Arm64.Reg.x2 = n ∧
                Arm64.CType.SemType.valWf Arm64.CType.U32 c ∧ Arm64.CType.SemType.valWf Arm64.CType.SizeT n⌝ ∗
        Arm64.memRegion dst (BitVec.toNat n),
  post := fun x s0 sf =>
    match x with
    | (dst, c, n) =>
      ⌜Arm64.CType.SemType.pureWf Arm64.CType.MutSlice8 dst (List.replicate (BitVec.toNat n) (BitVec.setWidth 8 c)) ∧
            Arm64.State.readReg64 sf Arm64.Reg.x0 = dst⌝ ∗
        Arm64.CType.SemType.interp Arm64.CType.MutSlice8 dst (List.replicate (BitVec.toNat n) (BitVec.setWidth 8 c)) }

/-- `memcmp(s1, s2, n)` on disjoint mutable/shared byte slices `s1 ↦ₛ bs1`, `s2 ↦ₛ bs2`:
    returns `memcmpBytes bs1 bs2` (`0` iff `bs1 = bs2`). -/
def memcmpSpec : Arm64.Spec
  (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8)) :=
{
  pre := fun x s0 =>
    match x with
    | (s1, s2, n, bs1, bs2) =>
      ⌜Arm64.State.readReg64 s0 Arm64.Reg.x0 = s1 ∧
            Arm64.State.readReg64 s0 Arm64.Reg.x1 = s2 ∧
              Arm64.State.readReg64 s0 Arm64.Reg.x2 = n ∧
                Arm64.CType.SemType.pureWf Arm64.CType.ShrSlice8 s1 bs1 ∧
                  Arm64.CType.SemType.pureWf Arm64.CType.ShrSlice8 s2 bs2 ∧
                    Arm64.CType.SemType.valWf (VerifiedLibraries.Musl.SliceLenPair bs1 bs2) n⌝ ∗
        Arm64.CType.SemType.interp Arm64.CType.ShrSlice8 s1 bs1 ∗
          Arm64.CType.SemType.interp Arm64.CType.ShrSlice8 s2 bs2,
  post := fun x s0 sf =>
    match x with
    | (s1, s2, n, bs1, bs2) =>
      ⌜Arm64.State.readReg32 sf Arm64.Reg.x0 = VerifiedLibraries.Musl.memcmpBytes bs1 bs2⌝ ∗
        Arm64.CType.SemType.interp Arm64.CType.ShrSlice8 s1 bs1 ∗
          Arm64.CType.SemType.interp Arm64.CType.ShrSlice8 s2 bs2 }

/-- `memcmp(s1, s2, n)` on read-only byte slices `s1 ↦ᵣ bs1`, `s2 ↦ᵣ bs2`:
    returns `memcmpBytes bs1 bs2` (`0` iff `bs1 = bs2`). -/
def memcmpROSpec : Arm64.Spec
  (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8)) :=
{
  pre := fun x s0 =>
    match x with
    | (s1, s2, n, bs1, bs2) =>
      ⌜Arm64.State.readReg64 s0 Arm64.Reg.x0 = s1 ∧
            Arm64.State.readReg64 s0 Arm64.Reg.x1 = s2 ∧
              Arm64.State.readReg64 s0 Arm64.Reg.x2 = n ∧
                Arm64.CType.SemType.pureWf VerifiedLibraries.Musl.RoSlice8 s1 bs1 ∧
                  Arm64.CType.SemType.pureWf VerifiedLibraries.Musl.RoSlice8 s2 bs2 ∧
                    Arm64.CType.SemType.valWf (VerifiedLibraries.Musl.SliceLenPair bs1 bs2) n⌝ ∗
        Arm64.CType.SemType.interp VerifiedLibraries.Musl.RoSlice8 s1 bs1 ∗
          Arm64.CType.SemType.interp VerifiedLibraries.Musl.RoSlice8 s2 bs2,
  post := fun x s0 sf =>
    match x with
    | (s1, s2, n, bs1, bs2) =>
      ⌜Arm64.State.readReg32 sf Arm64.Reg.x0 = VerifiedLibraries.Musl.memcmpBytes bs1 bs2⌝ ∗
        Arm64.CType.SemType.interp VerifiedLibraries.Musl.RoSlice8 s1 bs1 ∗
          Arm64.CType.SemType.interp VerifiedLibraries.Musl.RoSlice8 s2 bs2 }

/-- `bcmp(s1, s2, n)` on disjoint mutable/shared byte slices `s1 ↦ₛ bs1`, `s2 ↦ₛ bs2`:
    tail-calls `memcmp` and returns `memcmpBytes bs1 bs2` (`0` iff `bs1 = bs2`). -/
def bcmpSpec : Arm64.Spec
  (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8)) :=
{
  pre := fun x s0 =>
    match x with
    | (s1, s2, n, bs1, bs2) =>
      ⌜Arm64.State.readReg64 s0 Arm64.Reg.x0 = s1 ∧
            Arm64.State.readReg64 s0 Arm64.Reg.x1 = s2 ∧
              Arm64.State.readReg64 s0 Arm64.Reg.x2 = n ∧
                Arm64.CType.SemType.pureWf Arm64.CType.ShrSlice8 s1 bs1 ∧
                  Arm64.CType.SemType.pureWf Arm64.CType.ShrSlice8 s2 bs2 ∧
                    Arm64.CType.SemType.valWf (VerifiedLibraries.Musl.SliceLenPair bs1 bs2) n⌝ ∗
        Arm64.CType.SemType.interp Arm64.CType.ShrSlice8 s1 bs1 ∗
          Arm64.CType.SemType.interp Arm64.CType.ShrSlice8 s2 bs2,
  post := fun x s0 sf =>
    match x with
    | (s1, s2, n, bs1, bs2) =>
      ⌜Arm64.State.readReg32 sf Arm64.Reg.x0 = VerifiedLibraries.Musl.memcmpBytes bs1 bs2⌝ ∗
        Arm64.CType.SemType.interp Arm64.CType.ShrSlice8 s1 bs1 ∗
          Arm64.CType.SemType.interp Arm64.CType.ShrSlice8 s2 bs2 }

/-- `bcmp(s1, s2, n)` on read-only byte slices `s1 ↦ᵣ bs1`, `s2 ↦ᵣ bs2`:
    tail-calls `memcmp` and returns `memcmpBytes bs1 bs2` (`0` iff `bs1 = bs2`). -/
def bcmpROSpec : Arm64.Spec
  (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8)) :=
{
  pre := fun x s0 =>
    match x with
    | (s1, s2, n, bs1, bs2) =>
      ⌜Arm64.State.readReg64 s0 Arm64.Reg.x0 = s1 ∧
            Arm64.State.readReg64 s0 Arm64.Reg.x1 = s2 ∧
              Arm64.State.readReg64 s0 Arm64.Reg.x2 = n ∧
                Arm64.CType.SemType.pureWf VerifiedLibraries.Musl.RoSlice8 s1 bs1 ∧
                  Arm64.CType.SemType.pureWf VerifiedLibraries.Musl.RoSlice8 s2 bs2 ∧
                    Arm64.CType.SemType.valWf (VerifiedLibraries.Musl.SliceLenPair bs1 bs2) n⌝ ∗
        Arm64.CType.SemType.interp VerifiedLibraries.Musl.RoSlice8 s1 bs1 ∗
          Arm64.CType.SemType.interp VerifiedLibraries.Musl.RoSlice8 s2 bs2,
  post := fun x s0 sf =>
    match x with
    | (s1, s2, n, bs1, bs2) =>
      ⌜Arm64.State.readReg32 sf Arm64.Reg.x0 = VerifiedLibraries.Musl.memcmpBytes bs1 bs2⌝ ∗
        Arm64.CType.SemType.interp VerifiedLibraries.Musl.RoSlice8 s1 bs1 ∗
          Arm64.CType.SemType.interp VerifiedLibraries.Musl.RoSlice8 s2 bs2 }

/-- `memchr(s, c, n)` on a mutable/shared byte slice `s ↦ₛ bs`: returns a pointer to the first
    occurrence of `c.setWidth 8` in `bs`, or `0` (`NULL`) if not found. -/
def memchrSpec : Arm64.Spec (BitVec 64 × BitVec 32 × BitVec 64 × List (BitVec 8)) :=
{
  pre := fun x s0 =>
    match x with
    | (s, c, n, bs) =>
      ⌜Arm64.State.readReg64 s0 Arm64.Reg.x0 = s ∧
            Arm64.State.readReg32 s0 Arm64.Reg.x1 = c ∧
              Arm64.State.readReg64 s0 Arm64.Reg.x2 = n ∧
                Arm64.CType.SemType.pureWf Arm64.CType.ShrSlice8 s bs ∧
                  Arm64.CType.SemType.valWf Arm64.CType.U32 c ∧ Arm64.CType.SemType.valWf (Arm64.CType.SliceLen bs) n⌝ ∗
        Arm64.CType.SemType.interp Arm64.CType.ShrSlice8 s bs,
  post := fun x s0 sf =>
    match x with
    | (s, c, n, bs) =>
      ⌜Arm64.State.readReg64 sf Arm64.Reg.x0 = VerifiedLibraries.Musl.memchrRet s bs (BitVec.setWidth 8 c)⌝ ∗
        Arm64.CType.SemType.interp Arm64.CType.ShrSlice8 s bs }

/-- `memchr(s, c, n)` on a read-only byte slice `s ↦ᵣ bs`: returns a pointer to the first
    occurrence of `c.setWidth 8` in `bs`, or `0` (`NULL`) if not found. -/
def memchrROSpec : Arm64.Spec (BitVec 64 × BitVec 32 × BitVec 64 × List (BitVec 8)) :=
{
  pre := fun x s0 =>
    match x with
    | (s, c, n, bs) =>
      ⌜Arm64.State.readReg64 s0 Arm64.Reg.x0 = s ∧
            Arm64.State.readReg32 s0 Arm64.Reg.x1 = c ∧
              Arm64.State.readReg64 s0 Arm64.Reg.x2 = n ∧
                Arm64.CType.SemType.pureWf VerifiedLibraries.Musl.RoSlice8 s bs ∧
                  Arm64.CType.SemType.valWf Arm64.CType.U32 c ∧ Arm64.CType.SemType.valWf (Arm64.CType.SliceLen bs) n⌝ ∗
        Arm64.CType.SemType.interp VerifiedLibraries.Musl.RoSlice8 s bs,
  post := fun x s0 sf =>
    match x with
    | (s, c, n, bs) =>
      ⌜Arm64.State.readReg64 sf Arm64.Reg.x0 = VerifiedLibraries.Musl.memchrRet s bs (BitVec.setWidth 8 c)⌝ ∗
        Arm64.CType.SemType.interp VerifiedLibraries.Musl.RoSlice8 s bs }

/-- `memrchr(s, c, n)` / `__memrchr(s, c, n)` on a mutable/shared byte slice `s ↦ₛ bs`:
    returns a pointer to the last occurrence of `c.setWidth 8` in `bs`, or `0` (`NULL`) if not found. -/
def memrchrSpec : Arm64.Spec (BitVec 64 × BitVec 32 × BitVec 64 × List (BitVec 8)) :=
{
  pre := fun x s0 =>
    match x with
    | (s, c, n, bs) =>
      ⌜Arm64.State.readReg64 s0 Arm64.Reg.x0 = s ∧
            Arm64.State.readReg32 s0 Arm64.Reg.x1 = c ∧
              Arm64.State.readReg64 s0 Arm64.Reg.x2 = n ∧
                Arm64.CType.SemType.pureWf Arm64.CType.ShrSlice8 s bs ∧
                  Arm64.CType.SemType.valWf Arm64.CType.U32 c ∧ Arm64.CType.SemType.valWf (Arm64.CType.SliceLen bs) n⌝ ∗
        Arm64.CType.SemType.interp Arm64.CType.ShrSlice8 s bs,
  post := fun x s0 sf =>
    match x with
    | (s, c, n, bs) =>
      ⌜Arm64.State.readReg64 sf Arm64.Reg.x0 = VerifiedLibraries.Musl.memrchrRet s bs (BitVec.setWidth 8 c)⌝ ∗
        Arm64.CType.SemType.interp Arm64.CType.ShrSlice8 s bs }

/-- `memrchr(s, c, n)` / `__memrchr(s, c, n)` on a read-only byte slice `s ↦ᵣ bs`:
    returns a pointer to the last occurrence of `c.setWidth 8` in `bs`, or `0` (`NULL`) if not found. -/
def memrchrROSpec : Arm64.Spec (BitVec 64 × BitVec 32 × BitVec 64 × List (BitVec 8)) :=
{
  pre := fun x s0 =>
    match x with
    | (s, c, n, bs) =>
      ⌜Arm64.State.readReg64 s0 Arm64.Reg.x0 = s ∧
            Arm64.State.readReg32 s0 Arm64.Reg.x1 = c ∧
              Arm64.State.readReg64 s0 Arm64.Reg.x2 = n ∧
                Arm64.CType.SemType.pureWf VerifiedLibraries.Musl.RoSlice8 s bs ∧
                  Arm64.CType.SemType.valWf Arm64.CType.U32 c ∧ Arm64.CType.SemType.valWf (Arm64.CType.SliceLen bs) n⌝ ∗
        Arm64.CType.SemType.interp VerifiedLibraries.Musl.RoSlice8 s bs,
  post := fun x s0 sf =>
    match x with
    | (s, c, n, bs) =>
      ⌜Arm64.State.readReg64 sf Arm64.Reg.x0 = VerifiedLibraries.Musl.memrchrRet s bs (BitVec.setWidth 8 c)⌝ ∗
        Arm64.CType.SemType.interp VerifiedLibraries.Musl.RoSlice8 s bs }

/-- `memccpy(dst, src, c, n)` from a mutable/shared byte slice `src ↦ₛ bs`: copies bytes from
    `src` to `dst` up to and including the first occurrence of `c.setWidth 8` (or all `n` bytes
    if `c.setWidth 8 ∉ bs`), returning `dst + (k + 1)` on match or `0` (`NULL`) if not found. -/
def memccpySpec : Arm64.Spec
  (BitVec 64 × BitVec 64 × BitVec 32 × BitVec 64 × List (BitVec 8)) :=
{
  pre := fun x s0 =>
    match x with
    | (dst, src, c, n, bs) =>
      ⌜Arm64.State.readReg64 s0 Arm64.Reg.x0 = dst ∧
            Arm64.State.readReg64 s0 Arm64.Reg.x1 = src ∧
              Arm64.State.readReg32 s0 Arm64.Reg.x2 = c ∧
                Arm64.State.readReg64 s0 Arm64.Reg.x3 = n ∧
                  Arm64.CType.SemType.pureWf Arm64.CType.ShrSlice8 src bs ∧
                    Arm64.CType.SemType.valWf Arm64.CType.U32 c ∧
                      Arm64.CType.SemType.valWf (Arm64.CType.SliceLen bs) n⌝ ∗
        Arm64.memRegion dst (List.length bs) ∗ Arm64.CType.SemType.interp Arm64.CType.ShrSlice8 src bs,
  post := fun x s0 sf =>
    match x with
    | (dst, src, c, n, bs) =>
      ⌜Arm64.CType.SemType.pureWf (VerifiedLibraries.Musl.PrefixBuf (List.length bs)) dst
              (List.take (VerifiedLibraries.Musl.memccpyCount bs (BitVec.setWidth 8 c)) bs) ∧
            Arm64.State.readReg64 sf Arm64.Reg.x0 = VerifiedLibraries.Musl.memccpyRet dst bs (BitVec.setWidth 8 c)⌝ ∗
        Arm64.CType.SemType.interp (VerifiedLibraries.Musl.PrefixBuf (List.length bs)) dst
            (List.take (VerifiedLibraries.Musl.memccpyCount bs (BitVec.setWidth 8 c)) bs) ∗
          Arm64.CType.SemType.interp Arm64.CType.ShrSlice8 src bs }

/-- `memccpy(dst, src, c, n)` from a read-only byte slice `src ↦ᵣ bs`: copies bytes from
    `src` to `dst` up to and including the first occurrence of `c.setWidth 8` (or all `n` bytes
    if `c.setWidth 8 ∉ bs`), returning `dst + (k + 1)` on match or `0` (`NULL`) if not found. -/
def memccpyROSpec : Arm64.Spec
  (BitVec 64 × BitVec 64 × BitVec 32 × BitVec 64 × List (BitVec 8)) :=
{
  pre := fun x s0 =>
    match x with
    | (dst, src, c, n, bs) =>
      ⌜Arm64.State.readReg64 s0 Arm64.Reg.x0 = dst ∧
            Arm64.State.readReg64 s0 Arm64.Reg.x1 = src ∧
              Arm64.State.readReg32 s0 Arm64.Reg.x2 = c ∧
                Arm64.State.readReg64 s0 Arm64.Reg.x3 = n ∧
                  Arm64.CType.SemType.pureWf VerifiedLibraries.Musl.RoSlice8 src bs ∧
                    Arm64.CType.SemType.valWf Arm64.CType.U32 c ∧
                      Arm64.CType.SemType.valWf (Arm64.CType.SliceLen bs) n⌝ ∗
        Arm64.memRegion dst (List.length bs) ∗ Arm64.CType.SemType.interp VerifiedLibraries.Musl.RoSlice8 src bs,
  post := fun x s0 sf =>
    match x with
    | (dst, src, c, n, bs) =>
      ⌜Arm64.CType.SemType.pureWf (VerifiedLibraries.Musl.PrefixBuf (List.length bs)) dst
              (List.take (VerifiedLibraries.Musl.memccpyCount bs (BitVec.setWidth 8 c)) bs) ∧
            Arm64.State.readReg64 sf Arm64.Reg.x0 = VerifiedLibraries.Musl.memccpyRet dst bs (BitVec.setWidth 8 c)⌝ ∗
        Arm64.CType.SemType.interp (VerifiedLibraries.Musl.PrefixBuf (List.length bs)) dst
            (List.take (VerifiedLibraries.Musl.memccpyCount bs (BitVec.setWidth 8 c)) bs) ∗
          Arm64.CType.SemType.interp VerifiedLibraries.Musl.RoSlice8 src bs }

/-- `mempcpy(dst, src, n)` from a mutable/shared byte slice `src ↦ₛ bs`: copies `n = bs.length`
    bytes to disjoint uninitialized buffer `dst` and returns `dst + n`. -/
def mempcpySpec : Arm64.Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8)) :=
{
  pre := fun x s0 =>
    match x with
    | (dst, src, n, bs) =>
      ⌜Arm64.State.readReg64 s0 Arm64.Reg.x0 = dst ∧
            Arm64.State.readReg64 s0 Arm64.Reg.x1 = src ∧
              Arm64.State.readReg64 s0 Arm64.Reg.x2 = n ∧
                Arm64.CType.SemType.pureWf Arm64.CType.ShrSlice8 src bs ∧
                  Arm64.CType.SemType.valWf (Arm64.CType.SliceLen bs) n⌝ ∗
        Arm64.memRegion dst (List.length bs) ∗
          Arm64.CType.SemType.interp Arm64.CType.ShrSlice8 src bs ∗ Arm64.stackFrameAt (Arm64.State.sp s0) 32,
  post := fun x s0 sf =>
    match x with
    | (dst, src, n, bs) =>
      ⌜Arm64.CType.SemType.pureWf Arm64.CType.MutSlice8 dst bs ∧ Arm64.State.readReg64 sf Arm64.Reg.x0 = dst + n⌝ ∗
        Arm64.CType.SemType.interp Arm64.CType.MutSlice8 dst bs ∗
          Arm64.CType.SemType.interp Arm64.CType.ShrSlice8 src bs ∗ Arm64.stackFrameAt (Arm64.State.sp sf) 32 }

/-- `mempcpy(dst, src, n)` from a read-only byte slice `src ↦ᵣ bs`: copies `n = bs.length`
    bytes to disjoint uninitialized buffer `dst` and returns `dst + n`. -/
def mempcpyROSpec : Arm64.Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8)) :=
{
  pre := fun x s0 =>
    match x with
    | (dst, src, n, bs) =>
      ⌜Arm64.State.readReg64 s0 Arm64.Reg.x0 = dst ∧
            Arm64.State.readReg64 s0 Arm64.Reg.x1 = src ∧
              Arm64.State.readReg64 s0 Arm64.Reg.x2 = n ∧
                Arm64.CType.SemType.pureWf VerifiedLibraries.Musl.RoSlice8 src bs ∧
                  Arm64.CType.SemType.valWf (Arm64.CType.SliceLen bs) n⌝ ∗
        Arm64.memRegion dst (List.length bs) ∗
          Arm64.CType.SemType.interp VerifiedLibraries.Musl.RoSlice8 src bs ∗ Arm64.stackFrameAt (Arm64.State.sp s0) 32,
  post := fun x s0 sf =>
    match x with
    | (dst, src, n, bs) =>
      ⌜Arm64.CType.SemType.pureWf Arm64.CType.MutSlice8 dst bs ∧ Arm64.State.readReg64 sf Arm64.Reg.x0 = dst + n⌝ ∗
        Arm64.CType.SemType.interp Arm64.CType.MutSlice8 dst bs ∗
          Arm64.CType.SemType.interp VerifiedLibraries.Musl.RoSlice8 src bs ∗
            Arm64.stackFrameAt (Arm64.State.sp sf) 32 }

/-- `memmem(hs, k, ne, l)` on disjoint mutable/shared byte slices `hs ↦ₛ bsHay`, `ne ↦ₛ bsNee`:
    returns a pointer to the first occurrence of needle `bsNee` in haystack `bsHay`, or `0` (`NULL`)
    if not found (`hs` if `bsNee = []`). -/
def memmemSpec : Arm64.Spec
  (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8)) :=
{
  pre := fun x s0 =>
    match x with
    | (hs, k, ne, l, bsHay, bsNee) =>
      ⌜Arm64.State.readReg64 s0 Arm64.Reg.x0 = hs ∧
            Arm64.State.readReg64 s0 Arm64.Reg.x1 = k ∧
              Arm64.State.readReg64 s0 Arm64.Reg.x2 = ne ∧
                Arm64.State.readReg64 s0 Arm64.Reg.x3 = l ∧
                  Arm64.CType.SemType.pureWf Arm64.CType.ShrSlice8 hs bsHay ∧
                    Arm64.CType.SemType.valWf (Arm64.CType.SliceLen bsHay) k ∧
                      Arm64.CType.SemType.pureWf Arm64.CType.ShrSlice8 ne bsNee ∧
                        Arm64.CType.SemType.valWf (Arm64.CType.SliceLen bsNee) l ∧
                          0 < BitVec.toNat hs ∧
                            BitVec.toNat hs + List.length bsHay ≤ 2 ^ 64 ∧
                              (List.length bsNee ≤ 4 ∨ List.length bsHay < List.length bsNee)⌝ ∗
        Arm64.CType.SemType.interp Arm64.CType.ShrSlice8 hs bsHay ∗
          Arm64.CType.SemType.interp Arm64.CType.ShrSlice8 ne bsNee ∗ Arm64.stackFrameAt (Arm64.State.sp s0) 48,
  post := fun x s0 sf =>
    match x with
    | (hs, k, ne, l, bsHay, bsNee) =>
      ⌜Arm64.State.readReg64 sf Arm64.Reg.x0 = VerifiedLibraries.Musl.memmemRet hs bsHay bsNee⌝ ∗
        Arm64.CType.SemType.interp Arm64.CType.ShrSlice8 hs bsHay ∗
          Arm64.CType.SemType.interp Arm64.CType.ShrSlice8 ne bsNee ∗ Arm64.stackFrameAt (Arm64.State.sp sf) 48 }

/-- `memmem(hs, k, ne, l)` on read-only byte slices `hs ↦ᵣ bsHay`, `ne ↦ᵣ bsNee`:
    returns a pointer to the first occurrence of needle `bsNee` in haystack `bsHay`, or `0` (`NULL`)
    if not found (`hs` if `bsNee = []`). -/
def memmemROSpec : Arm64.Spec
  (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8)) :=
{
  pre := fun x s0 =>
    match x with
    | (hs, k, ne, l, bsHay, bsNee) =>
      ⌜Arm64.State.readReg64 s0 Arm64.Reg.x0 = hs ∧
            Arm64.State.readReg64 s0 Arm64.Reg.x1 = k ∧
              Arm64.State.readReg64 s0 Arm64.Reg.x2 = ne ∧
                Arm64.State.readReg64 s0 Arm64.Reg.x3 = l ∧
                  Arm64.CType.SemType.pureWf VerifiedLibraries.Musl.RoSlice8 hs bsHay ∧
                    Arm64.CType.SemType.valWf (Arm64.CType.SliceLen bsHay) k ∧
                      Arm64.CType.SemType.pureWf VerifiedLibraries.Musl.RoSlice8 ne bsNee ∧
                        Arm64.CType.SemType.valWf (Arm64.CType.SliceLen bsNee) l ∧
                          0 < BitVec.toNat hs ∧
                            BitVec.toNat hs + List.length bsHay ≤ 2 ^ 64 ∧
                              (List.length bsNee ≤ 4 ∨ List.length bsHay < List.length bsNee)⌝ ∗
        Arm64.CType.SemType.interp VerifiedLibraries.Musl.RoSlice8 hs bsHay ∗
          Arm64.CType.SemType.interp VerifiedLibraries.Musl.RoSlice8 ne bsNee ∗
            Arm64.stackFrameAt (Arm64.State.sp s0) 48,
  post := fun x s0 sf =>
    match x with
    | (hs, k, ne, l, bsHay, bsNee) =>
      ⌜Arm64.State.readReg64 sf Arm64.Reg.x0 = VerifiedLibraries.Musl.memmemRet hs bsHay bsNee⌝ ∗
        Arm64.CType.SemType.interp VerifiedLibraries.Musl.RoSlice8 hs bsHay ∗
          Arm64.CType.SemType.interp VerifiedLibraries.Musl.RoSlice8 ne bsNee ∗
            Arm64.stackFrameAt (Arm64.State.sp sf) 48 }

end VerifiedLibraries.Musl


