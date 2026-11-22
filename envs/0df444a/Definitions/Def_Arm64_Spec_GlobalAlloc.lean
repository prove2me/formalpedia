-- Prove2me | Definitions.Def_Arm64_Spec_GlobalAlloc
-- name    : Arm64_Spec_GlobalAlloc
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:20:38.275152+00:00
-- url     : https://prove2.me/theorems/afccd089-8b68-450b-b63d-bbf1e3a4a940
-- title:
--   Arm64.Trusted.Spec.GlobalAlloc — Generic Rust GlobalAlloc Specification
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted/Spec/GlobalAlloc.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Spec/GlobalAlloc.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/Spec/GlobalAlloc.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Spec/GlobalAlloc.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/Spec/GlobalAlloc.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
No other change.
-/

module

public import Definitions.Def_Arm64_Spec_RustHeap
public import Definitions.Def_Arm64_Spec_Placed

/-!
# Generic Rust `GlobalAlloc` Specification

Allocator-agnostic specification vocabulary for Rust `#[global_allocator]`
(`core::alloc::GlobalAlloc`) implementations and callers. Defines layout and alignment predicates
(`IsPow2Align`, `LayoutOk`), non-allocator state and VM preservation conditions
(`AllocStatePreserved`, `VmPreserved`), non-null budget bounds (`BudgetOk`), entry-point addresses
(`GlobalAllocAddrs`), relational contracts (`globalAllocSpec`, `globalAllocZeroedSpec`,
`globalDeallocSpec`, `globalReallocSpec`), and the verified allocator bundle (`GlobalAlloc`).
-/

@[expose] public section

namespace Arm64.Rust

open Arm64

/-! ## Layout, Alignment, and Preservation Predicates -/

/-- `align` is a non-zero power of two (`align ≠ 0` and `align & (align - 1) = 0`), matching
    Rust's `core::alloc::Layout` alignment invariant. -/
abbrev IsPow2Align (align : BitVec 64) : Prop :=
  align ≠ 0#64 ∧ (align &&& (align - 1#64)) = 0#64

instance (align : BitVec 64) : Decidable (IsPow2Align align) :=
  inferInstanceAs (Decidable (_ ∧ _))

def isPow2Align (align : BitVec 64) : Bool :=
  decide (IsPow2Align align)

/-- Valid non-zero-size `core::alloc::Layout` (`Layout::from_size_align` together with
    `GlobalAlloc`'s non-zero `size` precondition): `size ≠ 0`, `align` is a power of two, and
    `size + align ≤ 2 ^ 63` so rounding `size` up to a multiple of `align` fits in
    `isize::MAX = 2 ^ 63 - 1`. -/
abbrev LayoutOk (size align : BitVec 64) : Prop :=
  size ≠ 0#64 ∧ IsPow2Align align ∧ size.toNat + align.toNat ≤ 2 ^ 63

instance (size align : BitVec 64) : Decidable (LayoutOk size align) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def layoutOk (size align : BitVec 64) : Bool :=
  decide (LayoutOk size align)

/-- Non-allocator architectural and OS state preserved across a `GlobalAlloc` call:
    file system (`fs`), I/O and user trace (`trace`), signal dispositions (`sigActions`),
    thread pointer (`tpidrEl0`), and frozen memory (`s0.mem.KeepsFrozen sf.mem`).
    Note: `sigMask`, `sigPending`, and `sigAltStack` are not currently framed here; callers that
    rely on an allocator preserving the blocked/pending signal mask or alternate signal stack
    must establish that separately for the concrete allocator. -/
def AllocStatePreserved (s0 sf : State) : Prop :=
  sf.fs = s0.fs ∧
  sf.trace = s0.trace ∧
  sf.sigActions = s0.sigActions ∧
  sf.tpidrEl0 = s0.tpidrEl0 ∧
  s0.mem.KeepsFrozen sf.mem

/-- Virtual-memory and thread-pointer preservation condition for `GlobalAlloc.heap_transport`:
    holds across caller transitions `s → s'` that preserve `brkStart`, `brk`, `tpidrEl0`, and
    `mem.perm`. Transitions that alter `mem.perm` (such as direct `mmap`, `munmap`, or `mprotect`
    syscalls) require allocator-specific reasoning. -/
def VmPreserved (s s' : State) : Prop :=
  s'.brkStart = s.brkStart ∧
  s'.brk = s.brk ∧
  s'.tpidrEl0 = s.tpidrEl0 ∧
  s'.mem.perm = s.mem.perm

/-- Budget condition under which allocating `(size, align)` at usage `(liveBytes, liveBlocks)`
    returns a non-null pointer (`ret ≠ 0`) on normal `.Running` termination. -/
abbrev BudgetOk (maxGuaranteedAlign maxLiveBytes maxLiveBlocks liveBytes liveBlocks size align : Nat) :
    Prop :=
  align ≤ maxGuaranteedAlign ∧
  liveBytes + size ≤ maxLiveBytes ∧
  liveBlocks + 1 ≤ maxLiveBlocks

instance (maxGuaranteedAlign maxLiveBytes maxLiveBlocks liveBytes liveBlocks size align : Nat) :
    Decidable (BudgetOk maxGuaranteedAlign maxLiveBytes maxLiveBlocks liveBytes liveBlocks size align) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-! ## Entry-Point Addresses -/

/-- Code entry-point addresses for the four Rust `core::alloc::GlobalAlloc` ABI routines
    (`alloc`, `dealloc`, `realloc`, `alloc_zeroed`). -/
structure GlobalAllocAddrs where
  alloc        : BitVec 64
  dealloc      : BitVec 64
  realloc      : BitVec 64
  alloc_zeroed : BitVec 64
  deriving DecidableEq, Repr, Inhabited

namespace GlobalAllocAddrs

abbrev allocZeroed (addrs : GlobalAllocAddrs) : BitVec 64 := addrs.alloc_zeroed

/-- Resolve `GlobalAllocAddrs` from a `Program` by symbol name (defaulting to
    `__rust_{alloc,dealloc,realloc,alloc_zeroed}`). -/
def ofProgram (P : Program)
    (allocSym : String := "__rust_alloc")
    (deallocSym : String := "__rust_dealloc")
    (reallocSym : String := "__rust_realloc")
    (allocZeroedSym : String := "__rust_alloc_zeroed") : GlobalAllocAddrs where
  alloc        := P.fnAddr allocSym
  dealloc      := P.fnAddr deallocSym
  realloc      := P.fnAddr reallocSym
  alloc_zeroed := P.fnAddr allocZeroedSym

/-- Resolve `GlobalAllocAddrs` from a single-block `Obj.PlacedLib` under placement `pl`. -/
def ofPlacedLib (lib : Obj.PlacedLib) (pl : Obj.Placement)
    (allocSym : String := "__rust_alloc")
    (deallocSym : String := "__rust_dealloc")
    (reallocSym : String := "__rust_realloc")
    (allocZeroedSym : String := "__rust_alloc_zeroed") : GlobalAllocAddrs where
  alloc        := lib.fnAddr pl allocSym
  dealloc      := lib.fnAddr pl deallocSym
  realloc      := lib.fnAddr pl reallocSym
  alloc_zeroed := lib.fnAddr pl allocZeroedSym

/-- Resolve `GlobalAllocAddrs` from a multi-block `Obj.MultiPlacedLib` under placement `mpl`. -/
def ofMultiPlacedLib (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    (allocSym : String := "__rust_alloc")
    (deallocSym : String := "__rust_dealloc")
    (reallocSym : String := "__rust_realloc")
    (allocZeroedSym : String := "__rust_alloc_zeroed") : GlobalAllocAddrs where
  alloc        := lib.fnAddr mpl allocSym
  dealloc      := lib.fnAddr mpl deallocSym
  realloc      := lib.fnAddr mpl reallocSym
  alloc_zeroed := lib.fnAddr mpl allocZeroedSym

end GlobalAllocAddrs

/-! ## Relational Subroutine Contracts -/

/-- Contract for `GlobalAlloc::alloc(size, align)` (`__rust_alloc(size, align)`). Requires
    `LayoutOk size align`, `Heap liveBytes liveBlocks s0`, and `stackBytes` of caller stack scratch
    below `sp`. Returns `0#64` only when `BudgetOk` fails (leaving `Heap` unchanged); otherwise
    returns an `align`-aligned uninitialized block `Block ret size.toNat align.toNat ∗ memRegion ret size.toNat`
    and updates `Heap` to `(liveBytes + size.toNat, liveBlocks + 1)`. -/
def globalAllocSpec
    (Heap : Nat → Nat → State → SepProp)
    (Block : BitVec 64 → Nat → Nat → SepProp)
    (stackBytes maxGuaranteedAlign maxLiveBytes maxLiveBlocks : Nat) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × Nat × Nat) where
  pre := fun (size, align, sp, liveBytes, liveBlocks) s0 =>
    ⌜State.readReg64 s0 .x0 = size ∧ State.readReg64 s0 .x1 = align ∧
      State.sp s0 = sp ∧ LayoutOk size align⌝ ∗
    Heap liveBytes liveBlocks s0 ∗
    memRegion (sp - BitVec.ofNat 64 stackBytes) stackBytes
  post := fun (size, align, sp, liveBytes, liveBlocks) s0 sf =>
    ⌜AllocStatePreserved s0 sf⌝ ∗
    memRegion (sp - BitVec.ofNat 64 stackBytes) stackBytes ∗
    (if State.readReg64 sf .x0 = 0#64 then
       ⌜¬ BudgetOk maxGuaranteedAlign maxLiveBytes maxLiveBlocks
           liveBytes liveBlocks size.toNat align.toNat⌝ ∗
       Heap liveBytes liveBlocks sf
     else
       ⌜(State.readReg64 sf .x0).toNat % align.toNat = 0 ∧
         (State.readReg64 sf .x0).toNat + size.toNat < 2 ^ 64⌝ ∗
       Heap (liveBytes + size.toNat) (liveBlocks + 1) sf ∗
       Block (State.readReg64 sf .x0) size.toNat align.toNat ∗
       memRegion (State.readReg64 sf .x0) size.toNat)
  onOom := fun (_, _, _, _, _) _ _ => ⌜True⌝

/-- Contract for `GlobalAlloc::alloc_zeroed(size, align)` (`__rust_alloc_zeroed(size, align)`):
    same as `globalAllocSpec`, except a non-null return provides zero-initialized bytes
    `ret ↦ₛ List.replicate size.toNat 0#8`. -/
def globalAllocZeroedSpec
    (Heap : Nat → Nat → State → SepProp)
    (Block : BitVec 64 → Nat → Nat → SepProp)
    (stackBytes maxGuaranteedAlign maxLiveBytes maxLiveBlocks : Nat) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × Nat × Nat) where
  pre := fun (size, align, sp, liveBytes, liveBlocks) s0 =>
    ⌜State.readReg64 s0 .x0 = size ∧ State.readReg64 s0 .x1 = align ∧
      State.sp s0 = sp ∧ LayoutOk size align⌝ ∗
    Heap liveBytes liveBlocks s0 ∗
    memRegion (sp - BitVec.ofNat 64 stackBytes) stackBytes
  post := fun (size, align, sp, liveBytes, liveBlocks) s0 sf =>
    ⌜AllocStatePreserved s0 sf⌝ ∗
    memRegion (sp - BitVec.ofNat 64 stackBytes) stackBytes ∗
    (if State.readReg64 sf .x0 = 0#64 then
       ⌜¬ BudgetOk maxGuaranteedAlign maxLiveBytes maxLiveBlocks
           liveBytes liveBlocks size.toNat align.toNat⌝ ∗
       Heap liveBytes liveBlocks sf
     else
       ⌜(State.readReg64 sf .x0).toNat % align.toNat = 0 ∧
         (State.readReg64 sf .x0).toNat + size.toNat < 2 ^ 64⌝ ∗
       Heap (liveBytes + size.toNat) (liveBlocks + 1) sf ∗
       Block (State.readReg64 sf .x0) size.toNat align.toNat ∗
       (State.readReg64 sf .x0 ↦ₛ List.replicate size.toNat 0#8))
  onOom := fun (_, _, _, _, _) _ _ => ⌜True⌝

/-- Contract for `GlobalAlloc::dealloc(p, size, align)` (`__rust_dealloc(p, size, align)`):
    consumes `Block p size.toNat align.toNat ∗ memRegion p size.toNat`, updates `Heap` to
    `Heap (liveBytes - size.toNat) (liveBlocks - 1) sf`, and never terminates with `.OutOfMemory`. -/
def globalDeallocSpec
    (Heap : Nat → Nat → State → SepProp)
    (Block : BitVec 64 → Nat → Nat → SepProp)
    (stackBytes : Nat) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × Nat × Nat) where
  pre := fun (p, size, align, sp, liveBytes, liveBlocks) s0 =>
    ⌜State.readReg64 s0 .x0 = p ∧ State.readReg64 s0 .x1 = size ∧
      State.readReg64 s0 .x2 = align ∧ State.sp s0 = sp ∧ LayoutOk size align⌝ ∗
    Heap liveBytes liveBlocks s0 ∗
    Block p size.toNat align.toNat ∗
    memRegion p size.toNat ∗
    memRegion (sp - BitVec.ofNat 64 stackBytes) stackBytes
  post := fun (_, size, _, sp, liveBytes, liveBlocks) s0 sf =>
    ⌜AllocStatePreserved s0 sf⌝ ∗
    Heap (liveBytes - size.toNat) (liveBlocks - 1) sf ∗
    memRegion (sp - BitVec.ofNat 64 stackBytes) stackBytes

/-- Contract for `GlobalAlloc::realloc(p, oldSize, align, newSize)`
    (`__rust_realloc(p, oldSize, align, newSize)`). Given `LayoutOk oldSize align`,
    `LayoutOk newSize align`, and an initialized prefix `bs` with
    `bs.length ≤ min oldSize.toNat newSize.toNat`, returns `0#64` only when `BudgetOk` for
    `(newSize, align)` fails (leaving `Heap` and the old block with `bs` intact); otherwise
    consumes the old block and returns an `align`-aligned block of `newSize.toNat` bytes
    preserving `bs`, updating `Heap` to `(liveBytes - oldSize.toNat + newSize.toNat, liveBlocks)`. -/
def globalReallocSpec
    (Heap : Nat → Nat → State → SepProp)
    (Block : BitVec 64 → Nat → Nat → SepProp)
    (stackBytes maxGuaranteedAlign maxLiveBytes maxLiveBlocks : Nat) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × Nat × Nat) where
  pre := fun (p, oldSize, align, newSize, sp, bs, liveBytes, liveBlocks) s0 =>
    ⌜State.readReg64 s0 .x0 = p ∧ State.readReg64 s0 .x1 = oldSize ∧
      State.readReg64 s0 .x2 = align ∧ State.readReg64 s0 .x3 = newSize ∧
      State.sp s0 = sp ∧ LayoutOk oldSize align ∧ LayoutOk newSize align ∧
      bs.length ≤ oldSize.toNat ∧ bs.length ≤ newSize.toNat⌝ ∗
    Heap liveBytes liveBlocks s0 ∗
    Block p oldSize.toNat align.toNat ∗
    (p ↦ₛ bs) ∗
    memRegion (p + BitVec.ofNat 64 bs.length) (oldSize.toNat - bs.length) ∗
    memRegion (sp - BitVec.ofNat 64 stackBytes) stackBytes
  post := fun (p, oldSize, align, newSize, sp, bs, liveBytes, liveBlocks) s0 sf =>
    ⌜AllocStatePreserved s0 sf⌝ ∗
    memRegion (sp - BitVec.ofNat 64 stackBytes) stackBytes ∗
    (if State.readReg64 sf .x0 = 0#64 then
       ⌜¬ BudgetOk maxGuaranteedAlign maxLiveBytes maxLiveBlocks
           liveBytes liveBlocks newSize.toNat align.toNat⌝ ∗
       Heap liveBytes liveBlocks sf ∗
       Block p oldSize.toNat align.toNat ∗
       (p ↦ₛ bs) ∗
       memRegion (p + BitVec.ofNat 64 bs.length) (oldSize.toNat - bs.length)
     else
       ⌜(State.readReg64 sf .x0).toNat % align.toNat = 0 ∧
         (State.readReg64 sf .x0).toNat + newSize.toNat < 2 ^ 64⌝ ∗
       Heap (liveBytes - oldSize.toNat + newSize.toNat) liveBlocks sf ∗
       Block (State.readReg64 sf .x0) newSize.toNat align.toNat ∗
       (State.readReg64 sf .x0 ↦ₛ bs) ∗
       memRegion (State.readReg64 sf .x0 + BitVec.ofNat 64 bs.length)
         (newSize.toNat - bs.length))
  onOom := fun (_, _, _, _, _, _, _, _) _ _ => ⌜True⌝

/-! ## Verified `GlobalAlloc` Bundle -/

/-- Verified Rust `GlobalAlloc` implementation on program `P` at entry-point addresses `addrs`.
    Bundles the aggregate allocator invariant `Heap liveBytes liveBlocks s`, per-allocation token
    `Block p size align` (excluding byte contents), stack and budget parameters, non-null /
    alignment / non-wrapping proof obligations, `VmPreserved` invariance of `Heap`, and
    `subroutine_ok` proofs for all four ABI entry points. -/
structure GlobalAlloc (P : Program) (addrs : GlobalAllocAddrs) where
  Heap : Nat → Nat → State → SepProp
  Block : BitVec 64 → Nat → Nat → SepProp
  stackBytes : Nat
  maxGuaranteedAlign : Nat
  maxLiveBytes : Nat
  maxLiveBlocks : Nat
  noWrap :
    ∀ (p : BitVec 64) (size align : Nat),
      Block p size align ⊢ ⌜p.toNat + size ≤ 2 ^ 64⌝ ∗ Block p size align
  block_valid :
    ∀ (p : BitVec 64) (size align : Nat),
      Block p size align ⊢
        ⌜p ≠ 0#64 ∧ p.toNat % align = 0 ∧ p.toNat + size ≤ 2 ^ 64⌝ ∗ Block p size align
  heap_transport :
    ∀ (liveBytes liveBlocks : Nat) (s s' : State),
      VmPreserved s s' →
      Heap liveBytes liveBlocks s' = Heap liveBytes liveBlocks s
  alloc_ok :
    subroutine_ok P addrs.alloc
      (globalAllocSpec Heap Block stackBytes maxGuaranteedAlign maxLiveBytes maxLiveBlocks)
  alloc_zeroed_ok :
    subroutine_ok P addrs.alloc_zeroed
      (globalAllocZeroedSpec Heap Block stackBytes maxGuaranteedAlign maxLiveBytes maxLiveBlocks)
  dealloc_ok :
    subroutine_ok P addrs.dealloc
      (globalDeallocSpec Heap Block stackBytes)
  realloc_ok :
    subroutine_ok P addrs.realloc
      (globalReallocSpec Heap Block stackBytes maxGuaranteedAlign maxLiveBytes maxLiveBlocks)

namespace GlobalAlloc

variable {P : Program} {addrs : GlobalAllocAddrs}

abbrev budgetOk (A : GlobalAlloc P addrs) (liveBytes liveBlocks size align : Nat) : Prop :=
  BudgetOk A.maxGuaranteedAlign A.maxLiveBytes A.maxLiveBlocks liveBytes liveBlocks size align

abbrev allocSpec (A : GlobalAlloc P addrs) :=
  globalAllocSpec A.Heap A.Block A.stackBytes A.maxGuaranteedAlign A.maxLiveBytes A.maxLiveBlocks

abbrev allocZeroedSpec (A : GlobalAlloc P addrs) :=
  globalAllocZeroedSpec A.Heap A.Block A.stackBytes A.maxGuaranteedAlign A.maxLiveBytes A.maxLiveBlocks

abbrev deallocSpec (A : GlobalAlloc P addrs) :=
  globalDeallocSpec A.Heap A.Block A.stackBytes

abbrev reallocSpec (A : GlobalAlloc P addrs) :=
  globalReallocSpec A.Heap A.Block A.stackBytes A.maxGuaranteedAlign A.maxLiveBytes A.maxLiveBlocks

/-- Project `A.Block` to a fixed alignment `align`. -/
abbrev live (A : GlobalAlloc P addrs) (align : Nat) (p : BitVec 64) (size : Nat) : SepProp :=
  A.Block p size align

/-- Project `A` at fixed alignment `align` to an `Arm64.Rust.Allocator` with pool `pool`
    (default `emp` for representation predicates that depend only on `live`). -/
def atAlign (A : GlobalAlloc P addrs) (align : Nat) (pool : SepProp := emp) : Allocator where
  pool := pool
  live := A.live align
  noWrap p sz := A.noWrap p sz align

/-- `Vec<u8>` or `String` heap buffer over `A` (alignment 1). -/
abbrev vecBuf (A : GlobalAlloc P addrs) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  Arm64.Rust.vecBuf (A.atAlign 1) cap ptr bs

/-- `Vec<u8>` or `String` header at `v` with capacity `cap`, buffer `ptr`, and bytes `bs` over `A`. -/
abbrev vecAt (A : GlobalAlloc P addrs) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  Arm64.Rust.vecAt (A.atAlign 1) v cap ptr bs

/-- Existential `Vec<u8>` or `String` at `v` containing bytes `bs` over `A`. -/
abbrev vecOf (A : GlobalAlloc P addrs) (v : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  Arm64.Rust.vecOf (A.atAlign 1) v bs

/-- `Box<[u8]>` at `ptr` containing bytes `bs` over `A` (alignment 1). -/
abbrev boxAt (A : GlobalAlloc P addrs) (ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  Arm64.Rust.boxAt (A.atAlign 1) ptr bs

end GlobalAlloc

end Arm64.Rust


