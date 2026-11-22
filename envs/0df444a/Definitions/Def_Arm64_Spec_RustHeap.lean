-- Prove2me | Definitions.Def_Arm64_Spec_RustHeap
-- name    : Arm64_Spec_RustHeap
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:20:20.676714+00:00
-- url     : https://prove2.me/theorems/d5c7ae0b-3419-4a1c-a14c-2f860619cb5d
-- title:
--   Arm64.Trusted.Spec.RustHeap — Rust Heap Hook Vocabulary
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted/Spec/RustHeap.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Spec/RustHeap.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/Spec/RustHeap.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Spec/RustHeap.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/Spec/RustHeap.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
No other change.
-/

module

public import Definitions.Def_Arm64_Spec_Hoare

/-!
# Rust Heap Hook Vocabulary

Defines allocator-agnostic representation predicates (`vecBuf`, `vecHeader`, `vecAt`, `vecOf`,
`boxAt`) and external allocator hook contracts (`allocSpec`, `deallocSpec`, `shimSpec`) over an
abstract `Arm64.Allocator` at byte alignment (`1`). Specifications parameterize over these
contracts via `HookSat` without fixing a concrete allocator implementation.
-/

@[expose] public section

namespace Arm64.Rust

open Arm64

/-! ## Allocator and stack budget -/

/-- An abstract allocator: `pool` is its private state, `live p n` owns the live allocation of
    `n` bytes at `p` (without its contents), and `noWrap` witnesses `p.toNat + n ≤ 2 ^ 64`. -/
abbrev Allocator := Arm64.Allocator

/-- Stack bytes below `sp` that an extern hook may use. -/
abbrev hookStack : Nat := 4096

/-! ## Representation predicates -/

/-- `bs.length` fits in an `isize`. -/
abbrev SmallLen (n : Nat) : Prop := n < 2 ^ 63

/-- The heap buffer of a `Vec<u8>`/`String` with capacity `cap` at `ptr` holding bytes `bs`
    (`len = bs.length`). With `cap = 0` the buffer is a dangling non-null pointer. -/
def vecBuf (A : Allocator) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ SmallLen cap.toNat ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

/-- The 24-byte `Vec<u8>` header `{cap, ptr, len}` at `v`. -/
def vecHeader (v cap ptr len : BitVec 64) : SepProp :=
  (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ len)

/-- A `Vec<u8>`/`String` at `v` with capacity `cap`, buffer `ptr`, and contents `bs`. -/
def vecAt (A : Allocator) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗ vecBuf A cap ptr bs

/-- Some `Vec<u8>` at `v` with contents `bs`. -/
def vecOf (A : Allocator) (v : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, vecAt A v cap ptr bs

/-- A `Box<[u8]>` `(ptr, bs.length)` holding `bs`. -/
def boxAt (A : Allocator) (ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜ptr ≠ 0⌝ ∗ (if bs = [] then emp else A.live ptr bs.length ∗ (ptr ↦ₛ bs))

/-! ## Extern hook contracts -/

/-- The hook's stack: `hookStack` bytes below `sp`. -/
abbrev hookFrame (sp : BitVec 64) : SepProp :=
  memRegion (sp - BitVec.ofNat 64 hookStack) hookStack

/-- `__rust_alloc(n, 1)` / `__rust_alloc_zeroed(n, 1)` (with `zeroed`). Ghost: `(n, sp)`. -/
def allocSpec (A : Allocator) (zeroed : Bool) : Spec (BitVec 64 × BitVec 64) where
  pre := fun (n, sp) s0 =>
    ⌜State.readReg64 s0 .x0 = n ∧ State.readReg64 s0 .x1 = 1#64 ∧
      State.sp s0 = sp ∧ n ≠ 0 ∧ SmallLen n.toNat⌝ ∗
    A.pool ∗ hookFrame sp
  post := fun (n, sp) _s0 sf =>
    A.pool ∗ hookFrame sp ∗
      (if State.readReg64 sf .x0 = 0 then emp
       else A.live (State.readReg64 sf .x0) n.toNat ∗
         (if zeroed then (State.readReg64 sf .x0 ↦ₛ List.replicate n.toNat 0#8)
          else memRegion (State.readReg64 sf .x0) n.toNat))

/-- `__rust_dealloc(p, n, 1)`. Ghost: `(p, n, sp)`. -/
def deallocSpec (A : Allocator) : Spec (BitVec 64 × BitVec 64 × BitVec 64) where
  pre := fun (p, n, sp) s0 =>
    ⌜State.readReg64 s0 .x0 = p ∧ State.readReg64 s0 .x1 = n ∧
      State.readReg64 s0 .x2 = 1#64 ∧ State.sp s0 = sp⌝ ∗
    A.pool ∗ A.live p n.toNat ∗ memRegion p n.toNat ∗ hookFrame sp
  post := fun (_, _, sp) _s0 _sf =>
    A.pool ∗ hookFrame sp

/-- `__rust_no_alloc_shim_is_unstable_v2()`: does nothing. Ghost: `sp`. -/
def shimSpec : Spec (BitVec 64) where
  pre := fun sp s0 => ⌜State.sp s0 = sp⌝ ∗ hookFrame sp
  post := fun sp _s0 _sf => hookFrame sp

end Arm64.Rust


