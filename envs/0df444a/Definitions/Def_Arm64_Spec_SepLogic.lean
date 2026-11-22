-- Prove2me | Definitions.Def_Arm64_Spec_SepLogic
-- name    : Arm64_Spec_SepLogic
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:13:15.992442+00:00
-- url     : https://prove2.me/theorems/a7e4555c-6591-4493-a114-0166903d477a
-- title:
--   Arm64.Trusted.Spec.SepLogic — Byte-Granular Separation Logic Primitives
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted/Spec/SepLogic.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Spec/SepLogic.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/Spec/SepLogic.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Spec/SepLogic.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/Spec/SepLogic.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
No other change.
-/

module

public import Definitions.Def_Arm64_ISA_Memory
public import Definitions.Def_Arm64_ISA_State
public import Definitions.Def_Arm64_ISA_Semantics

/-!
# Byte-Granular Separation Logic Primitives

Defines byte-granular partial heaps (`Heap`, `GhostName`), nominal separation-logic propositions
and connectives (`SepProp`, `m ⊨ P`, `P ∗ Q`, `P -∗ Q`, `∃∗ x, P x`, `P ⊢ Q`, `|==> P`, `⌜φ⌝`),
multi-width points-to assertions (`↦₈`, `↦₁₆`, `↦₃₂`, `↦₆₄`, `↦₁₂₈`, `↦ₛ`, `↦₆₄*`, `↦₈ₙ`, `↦ₙ`,
and their read-only and lazy-free counterparts), byte regions (`InRegion`, `DisjointRegions`,
`regionBlock`, `memRegion`, `regionBlockProtNone`, `memRegionProtNone`), downward stack frames
(`stackFrame`, `stackFrame16`, `stackFrame32`, `stackFrameAt`), and abstract allocator interfaces
(`Allocator`, `AllocatorOom`).

`SepProp` is a nominal `structure` whose projection (`SepProp.holds`) and core connective/points-to
definitions live inside a plain `public section` (without `@[expose]`), keeping connective bodies
module-opaque to client proofs unless [`Arm64/Trusted/Spec/SepLogicModel.lean`](SepLogicModel.lean)
is imported explicitly. The partial commutative monoid laws for `Heap` and BI laws for `SepProp`
are verified in
[`Arm64/Testing/Tours/SepLogicLawsTour.lean`](../../Testing/Tours/SepLogicLawsTour.lean).
-/

namespace Arm64

@[expose] public section

/-! ## Memory Regions -/

/-- `a` lies in the `len`-byte region `[base, base + len)` (wrapping modulo `2^64`). -/
def InRegion (base : BitVec 64) (len : Nat) (a : BitVec 64) : Prop :=
  (a - base).toNat < len

instance instDecidableInRegion (base : BitVec 64) (len : Nat) (a : BitVec 64) :
    Decidable (InRegion base len a) :=
  inferInstanceAs (Decidable ((a - base).toNat < len))

/-- `a` lies outside the `len`-byte region `[base, base + len)`. -/
def OutsideRegion (base : BitVec 64) (len : Nat) (a : BitVec 64) : Prop :=
  len ≤ (a - base).toNat

/-- Two byte regions `[b₁, b₁ + n₁)` and `[b₂, b₂ + n₂)` are disjoint. -/
def DisjointRegions (b₁ : BitVec 64) (n₁ : Nat) (b₂ : BitVec 64) (n₂ : Nat) : Prop :=
  n₁ ≤ (b₂ - b₁).toNat ∧ n₂ ≤ (b₁ - b₂).toNat

/-- Every byte of `[base, base + len)` is deterministically readable in `m`
    (`(m.perm a).r = true` and `m.isLazyFree a = false`). -/
def Memory.Readable (m : Memory) (base : BitVec 64) (len : Nat) : Prop :=
  ∀ a : BitVec 64, InRegion base len a → (m.perm a).r = true ∧ m.isLazyFree a = false

/-- Every byte of `[base, base + len)` is mapped read-only (`some Perm.ro`) and not marked
    `lazyFree` (`m.isLazyFree a = false`) in `m`. -/
def Memory.RO (m : Memory) (base : BitVec 64) (len : Nat) : Prop :=
  ∀ a : BitVec 64, InRegion base len a → m.perm a = some Perm.ro ∧ m.isLazyFree a = false

/-- Every byte of `[base, base + len)` is mapped read-only (`Perm.ro`) in `m`. -/
abbrev memRO (m : Memory) (base : BitVec 64) (len : Nat) : Prop :=
  m.RO base len

/-! ## Partial Byte-Granular Heaps (`Heap`) -/

/-- Identifier for a ghost resource instance. -/
abbrev GhostName : Type := Nat

/-- A cell in a partial byte-granular heap: exclusive read-write (`rw`), duplicable read-only
    (`ro`), exclusive inaccessible `PROT_NONE` (`protNone`, preserving the underlying physical
    byte `b` across permission transitions per Linux `mm/mprotect.c` `mprotect_fixup` /
    `change_protection`), exclusive lazy-free read-write (`lazy`, owning a `Perm.rw` byte whose
    contents may be asynchronously zeroed by Linux `7.3` after `madvise(..., MADV_FREE)` until
    overwritten), or exclusive lazy-free `PROT_NONE` (`protNoneLazy`, owning a `Perm.protNone`
    byte whose lazy-free state persists across `mprotect(..., PROT_NONE)`). -/
inductive HeapCell where
  | rw (b : BitVec 8)
  | ro (b : BitVec 8)
  | protNone (b : BitVec 8)
  | lazy
  | protNoneLazy
  deriving DecidableEq, Repr, Inhabited

/-- A partial byte-granular heap mapping 64-bit addresses to optional physical heap cells (`phys`),
    together with ghost authoritative map entries (`auth`), ghost fragment entries (`frag`)
    indexed by `GhostName`, and virtual-address mapping reservation tokens (`mapped`). -/
@[ext]
structure Heap where
  /-- Physical byte cells (`rw`, `ro`, or `protNone`) at 64-bit addresses. -/
  phys : BitVec 64 → Option HeapCell
  /-- Authoritative ghost map slots: `auth γ k = some oa` owns key `k` at ghost name `γ` with
      authoritative value `oa : Option Nat`. -/
  auth : GhostName → BitVec 64 → Option (Option Nat) := fun _ _ => none
  /-- Fragment ghost map slots: `frag γ k = some v` owns key `k` at ghost name `γ` with value `v`. -/
  frag : GhostName → BitVec 64 → Option Nat := fun _ _ => none
  /-- Virtual-address mapping reservation token: `mapped a = true` asserts that byte `a` is
      currently mapped in `Memory` (`(m.perm a).mapped = true`), independent of physical byte-cell
      ownership (`phys a`). Owned exclusively (`h₁.mapped a = false ∨ h₂.mapped a = false`) so
      `mmap` can split a freshly mapped region into `memRegion base len` (handed to clients) and
      `memMapped base len` (retained by an allocator invariant to witness that the virtual address
      range remains mapped until `munmap`, which consumes both `memRegion` and `memMapped`). -/
  mapped : BitVec 64 → Bool := fun _ => false

instance : CoeFun Heap (fun _ => BitVec 64 → Option HeapCell) where
  coe := Heap.phys

namespace Heap

/-- The empty partial heap (nowhere defined). -/
def empty : Heap :=
  { phys := fun _ => none }

/-- Singleton read-write heap defined only at address `a` with byte value `b`. -/
def singleton (a : BitVec 64) (b : BitVec 8) : Heap :=
  { phys := fun x => if x = a then some (.rw b) else none }

/-- Singleton read-only heap defined only at address `a` with byte value `b`. -/
def singletonRO (a : BitVec 64) (b : BitVec 8) : Heap :=
  { phys := fun x => if x = a then some (.ro b) else none }

/-- Singleton `PROT_NONE` heap defined only at address `a` with preserved byte value `b`. -/
def singletonProtNone (a : BitVec 64) (b : BitVec 8) : Heap :=
  { phys := fun x => if x = a then some (.protNone b) else none }

/-- Singleton lazy-free read-write heap defined only at address `a`. -/
def singletonLazy (a : BitVec 64) : Heap :=
  { phys := fun x => if x = a then some .lazy else none }

/-- Two heaps are disjoint when at every physical address at least one is `none` (or both agree on
    the same read-only byte value), their ghost authoritative and fragment slots are pointwise
    disjoint, any authoritative slot in one heap agrees with any fragment slot at the same
    `(γ, k)` in the other heap, and their mapping reservation tokens are pointwise disjoint. -/
def Disjoint (h₁ h₂ : Heap) : Prop :=
  (∀ a, h₁.phys a = none ∨ h₂.phys a = none ∨
    ∃ b, h₁.phys a = some (.ro b) ∧ h₂.phys a = some (.ro b)) ∧
  (∀ γ k, h₁.auth γ k = none ∨ h₂.auth γ k = none) ∧
  (∀ γ k, h₁.frag γ k = none ∨ h₂.frag γ k = none) ∧
  (∀ γ k oa v,
    ((h₁.auth γ k = some oa ∧ h₂.frag γ k = some v) ∨
     (h₂.auth γ k = some oa ∧ h₁.frag γ k = some v)) → oa = some v) ∧
  (∀ a, h₁.mapped a = false ∨ h₂.mapped a = false)

/-- Left-biased union of two partial heaps (commutative when `h₁.Disjoint h₂`). -/
def union (h₁ h₂ : Heap) : Heap where
  phys a :=
    match h₁.phys a with
    | some b => some b
    | none   => h₂.phys a
  auth γ k :=
    match h₁.auth γ k with
    | some oa => some oa
    | none    => h₂.auth γ k
  frag γ k :=
    match h₁.frag γ k with
    | some v => some v
    | none   => h₂.frag γ k
  mapped a := h₁.mapped a || h₂.mapped a

/-- Ghost-state validity of a partial heap: only finitely many ghost names `γ` are in use, so a
    fresh `GhostName` can always be allocated. -/
def GhostValid (h : Heap) : Prop :=
  ∃ bound : Nat, ∀ γ, bound ≤ γ → ∀ k, h.auth γ k = none ∧ h.frag γ k = none

/-- A partial heap `h` matches total memory `m` when every allocated read-write byte `.rw b` in `h`
    agrees with `m.read8`, is mapped read-write (`some Perm.rw`), and is not `lazyFree`; every
    read-only byte `.ro b` in `h` agrees with `m.read8`, is readable (`(m.perm a).r = true`), and
    is not `lazyFree`; every inaccessible `PROT_NONE` byte `.protNone b` in `h` agrees with `m.read8`
    (`m.read8 a = b`, preserving the physical byte across permission transitions per Linux
    `mm/mprotect.c` `mprotect_fixup` / `change_protection`), has permission `some Perm.protNone`, and
    is not `lazyFree`; every lazy-free read-write byte `.lazy` in `h` is mapped read-write
    (`some Perm.rw`); every lazy-free inaccessible byte `.protNoneLazy` in `h` has permission
    `some Perm.protNone`; `h.GhostValid` holds; and every byte with `h.mapped a = true` is mapped
    anonymous in `m` (`(m.perm a).mapped = true ∧ m.isAnon a = true`). -/
def Matches (h : Heap) (m : Memory) : Prop :=
  (∀ a c, h.phys a = some c →
    match c with
    | .rw b => m.read8 a = b ∧ m.perm a = some Perm.rw ∧ m.isLazyFree a = false
    | .ro b => m.read8 a = b ∧ (m.perm a).r = true ∧ m.isLazyFree a = false
    | .protNone b => m.read8 a = b ∧ m.perm a = some Perm.protNone ∧ m.isLazyFree a = false
    | .lazy => m.perm a = some Perm.rw
    | .protNoneLazy => m.perm a = some Perm.protNone) ∧
  h.GhostValid ∧
  (∀ a, h.mapped a = true → (m.perm a).mapped = true ∧ m.isAnon a = true)

end Heap

/-- Partial heap owning `[base, base + len)` with byte values taken from `m`. -/
def regionHeap (base : BitVec 64) (len : Nat) (m : Memory) : Heap :=
  { phys := fun a => if InRegion base len a then some (.rw (m.read8 a)) else none }

/-- Partial heap owning `[base, base + len)` read-only with byte values taken from `m`. -/
def regionHeapRO (base : BitVec 64) (len : Nat) (m : Memory) : Heap :=
  { phys := fun a => if InRegion base len a then some (.ro (m.read8 a)) else none }

/-- Partial heap owning `[base, base + len)` as `PROT_NONE` with byte values taken from `m`. -/
def regionHeapProtNone (base : BitVec 64) (len : Nat) (m : Memory) : Heap :=
  { phys := fun a => if InRegion base len a then some (.protNone (m.read8 a)) else none }

/-- Partial heap owning `[base, base + len)` as lazy-free read-write bytes (`HeapCell.lazy`). -/
def regionHeapLazy (base : BitVec 64) (len : Nat) : Heap :=
  { phys := fun a => if InRegion base len a then some .lazy else none }

/-! ## Separation Logic Assertions (`SepProp`) -/

/-- Nominal separation logic assertion over partial heaps `Heap`.
    Connectives, points-to assertions, `Satisfies`, and `Entails` live in `public section` below
    (without `@[expose]`) so their definitions are module-opaque outside `import all
    Arm64.Trusted.Spec.SepLogic` (`Arm64.*` / `ProofLib.*`), while `CoeFun SepProp (fun _ => Heap → Prop)`
    lives solely in `Arm64.Trusted.Spec.SepLogicModel`. -/
@[ext]
structure SepProp where
  /-- Backing predicate over partial heaps `Heap`. -/
  holds : Heap → Prop

end -- @[expose] public section

public section

/-- Alias for `SepProp.holds` when explicitly stating semantic side conditions over a `Heap` in `Spec`. -/
abbrev SepProp.Holds (P : SepProp) (h : Heap) : Prop := P.holds h

namespace SepProp

/-- Memory `m` satisfies assertion `P` (`m ⊨ P`) when some sub-heap `h` satisfies `P.holds h` and matches `m`. -/
def Satisfies (P : SepProp) (m : Memory) : Prop :=
  ∃ h : Heap, P.holds h ∧ h.Matches m

/-- Semantic entailment between separation logic assertions (`P ⊢ Q`). -/
def Entails (P Q : SepProp) : Prop :=
  ∀ h : Heap, P.holds h → Q.holds h

/-- Frame-preserving update modality (`|==> P`): holds on `h` when for every memory `m` and
    disjoint frame `hf` with `(h.union hf).Matches m`, `h` can be updated to some `h'` satisfying
    `P.holds h'` that remains disjoint from `hf` with `(h'.union hf).Matches m`.

    Note: at the top-level memory satisfaction judgment `m ⊨ P`, `(m ⊨ |==> P) ↔ (m ⊨ P)`
    because `Satisfies` existentially quantifies over the heap `h : Heap` (including its ghost
    fields `auth` and `frag`) at each `⊨`. Within separation-logic entailments `P ⊢ |==> Q`,
    `bupd` enforces frame-preserving ghost updates (`bupd_frame_r`); across separate calls,
    ghost agreement is carried by packaging the authoritative ghost map inside an abstract
    invariant `I γ` alongside per-token fragments `T γ`. -/
@[inline] def bupd (P : SepProp) : SepProp :=
  ⟨fun h => ∀ (m : Memory) (hf : Heap), h.Disjoint hf → (h.union hf).Matches m →
    ∃ h' : Heap, P.holds h' ∧ h'.Disjoint hf ∧ (h'.union hf).Matches m⟩

/-- The empty heap assertion. -/
@[inline] def emp : SepProp := ⟨fun h => h = Heap.empty⟩

/-- `SepProp` that holds on every heap. -/
@[inline] def anyHeap : SepProp := ⟨fun _ => True⟩

/-- Pure proposition lifted into `SepProp` (`⌜φ⌝`). -/
@[inline] def pure (φ : Prop) : SepProp := ⟨fun h => h = Heap.empty ∧ φ⟩

/-- Separating conjunction (`P ∗ Q`): splits the heap into two disjoint sub-heaps satisfying `P` and `Q`. -/
@[inline] def sepConj (P Q : SepProp) : SepProp :=
  ⟨fun h => ∃ h₁ h₂ : Heap, h₁.Disjoint h₂ ∧ h = h₁.union h₂ ∧ P.holds h₁ ∧ Q.holds h₂⟩

/-- Separating implication / magic wand (`P -∗ Q`). -/
@[inline] def sepImp (P Q : SepProp) : SepProp :=
  ⟨fun h₁ => ∀ h₂ : Heap, h₁.Disjoint h₂ → P.holds h₂ → Q.holds (h₁.union h₂)⟩

universe u

/-- Existential quantification in separation logic (`∃∗ x, P x`). -/
@[inline] def sepExists {α : Sort u} (P : α → SepProp) : SepProp :=
  ⟨fun h => ∃ x : α, (P x).holds h⟩

end SepProp

export SepProp (Satisfies Entails bupd emp anyHeap sepConj sepImp sepExists)

notation:50 m:50 " ⊨ " P:51 => SepProp.Satisfies P m
infix:50 " ⊢ " => SepProp.Entails
prefix:58 "|==> " => SepProp.bupd
notation "⌜" φ "⌝" => SepProp.pure φ
infixr:60 " ∗ " => SepProp.sepConj
infixr:55 " -∗ " => SepProp.sepImp
notation:65 "∃∗ " x ", " P => SepProp.sepExists (fun x => P)
notation:65 "∃∗ " x " : " α ", " P => SepProp.sepExists (fun (x : α) => P)

set_option linter.defProp false in
/-- Duplicate a pure separation-logic assertion (`⌜φ⌝ ⊢ ⌜φ⌝ ∗ ⌜φ⌝`). -/
def SepProp.pure_dup (φ : Prop) : (⌜φ⌝ : SepProp) ⊢ ⌜φ⌝ ∗ ⌜φ⌝ :=
  fun _ ⟨he, hφ⟩ =>
    ⟨Heap.empty, Heap.empty,
      ⟨fun _ => Or.inl rfl, fun _ _ => Or.inl rfl, fun _ _ => Or.inl rfl,
       fun _ _ _ _ h => h.elim (fun ⟨h1, _⟩ => nomatch h1) (fun ⟨h1, _⟩ => nomatch h1),
       fun _ => Or.inl rfl⟩,
      he, ⟨rfl, hφ⟩, ⟨rfl, hφ⟩⟩

/-! ## Points-To Assertions, Regions, and Stack Frames -/

/-- Single-byte points-to assertion (`a ↦₈ v`). -/
@[inline] def pointsTo8 (a : BitVec 64) (v : BitVec 8) : SepProp :=
  ⟨fun h => h = Heap.singleton a v⟩

/-- Contiguous byte-list points-to assertion (`a ↦ₛ bs`). -/
def pointsToBytes (a : BitVec 64) : List (BitVec 8) → SepProp
  | []      => emp
  | b :: bs => pointsTo8 a b ∗ pointsToBytes (a + 1#64) bs

/-- Single-byte read-only points-to assertion (`a ↦₈ᵣ v`): requires only `(m.perm a).r = true`
    and is duplicable (`(a ↦₈ᵣ v) ∗ (a ↦₈ᵣ v) = (a ↦₈ᵣ v)`). -/
@[inline] def pointsTo8RO (a : BitVec 64) (v : BitVec 8) : SepProp :=
  ⟨fun h => h = Heap.singletonRO a v⟩

/-- Contiguous byte-list read-only points-to assertion (`a ↦ᵣ bs`). -/
def pointsToBytesRO (a : BitVec 64) : List (BitVec 8) → SepProp
  | []      => emp
  | b :: bs => pointsTo8RO a b ∗ pointsToBytesRO (a + 1#64) bs

/-- Single-byte `PROT_NONE` points-to assertion (`a ↦₈ₙ v`): owns byte `a` exclusively with
    permission `some Perm.protNone` and preserved physical byte value `v` (per Linux
    `mm/mprotect.c` `mprotect_fixup` / `change_protection`). -/
@[inline] def pointsTo8ProtNone (a : BitVec 64) (v : BitVec 8) : SepProp :=
  ⟨fun h => h = Heap.singletonProtNone a v⟩

/-- Contiguous byte-list `PROT_NONE` points-to assertion (`a ↦ₙ bs`). -/
def pointsToBytesProtNone (a : BitVec 64) : List (BitVec 8) → SepProp
  | []      => emp
  | b :: bs => pointsTo8ProtNone a b ∗ pointsToBytesProtNone (a + 1#64) bs

/-- Single-byte lazy-free read-write points-to assertion (`a ↦₈ₗ` / `a ↦ₗ`): owns byte `a`
    exclusively with permission `some Perm.rw` and indeterminate `lazyFree` state (produced by
    `madvise(..., MADV_FREE)` and upgraded back to `a ↦₈ v` by a store or `MADV_DONTNEED`). -/
@[inline] def pointsTo8Lazy (a : BitVec 64) : SepProp :=
  ⟨fun h => h = Heap.singletonLazy a⟩

/-- Separation logic assertion owning `[base, base + len)` matching memory `m`. -/
@[inline] def regionBlock (base : BitVec 64) (len : Nat) (m : Memory) : SepProp :=
  ⟨fun h => h = regionHeap base len m⟩

/-- Separation logic assertion owning `[base, base + len)` read-only matching memory `m`. -/
@[inline] def regionBlockRO (base : BitVec 64) (len : Nat) (m : Memory) : SepProp :=
  ⟨fun h => h = regionHeapRO base len m⟩

/-- Separation logic assertion owning `[base, base + len)` as `PROT_NONE` matching memory `m`. -/
@[inline] def regionBlockProtNone (base : BitVec 64) (len : Nat) (m : Memory) : SepProp :=
  ⟨fun h => h = regionHeapProtNone base len m⟩

/-- Separation logic assertion owning `[base, base + len)` with existential memory contents. -/
@[inline] def memRegion (base : BitVec 64) (len : Nat) : SepProp :=
  ∃∗ m : Memory, regionBlock base len m

/-- Separation logic assertion owning `[base, base + len)` as `PROT_NONE` with existential
    preserved memory contents. -/
@[inline] def memRegionProtNone (base : BitVec 64) (len : Nat) : SepProp :=
  ∃∗ m : Memory, regionBlockProtNone base len m

/-- Separation logic assertion owning `[base, base + len)` as lazy-free read-write memory
    (`HeapCell.lazy`), produced by `madvise(..., MADV_FREE)` and upgraded back to `memRegion`
    by stores or `MADV_DONTNEED`. -/
@[inline] def memRegionLazy (base : BitVec 64) (len : Nat) : SepProp :=
  ⟨fun h => h = regionHeapLazy base len⟩

end -- public section

@[expose] public section

/-- 16-bit little-endian points-to assertion (`a ↦₁₆ v`). -/
def pointsTo16 (a : BitVec 64) (v : BitVec 16) : SepProp :=
  pointsTo8 (a + 0#64) (v.extractLsb' 0 8) ∗
  pointsTo8 (a + 1#64) (v.extractLsb' 8 8)

/-- 32-bit little-endian points-to assertion (`a ↦₃₂ v`). -/
def pointsTo32 (a : BitVec 64) (v : BitVec 32) : SepProp :=
  pointsTo8 (a + 0#64) (v.extractLsb' 0 8) ∗
  pointsTo8 (a + 1#64) (v.extractLsb' 8 8) ∗
  pointsTo8 (a + 2#64) (v.extractLsb' 16 8) ∗
  pointsTo8 (a + 3#64) (v.extractLsb' 24 8)

/-- 64-bit little-endian points-to assertion (`a ↦₆₄ v`). -/
def pointsTo64 (a : BitVec 64) (v : BitVec 64) : SepProp :=
  pointsTo8 (a + 0#64) (v.extractLsb' 0 8) ∗
  pointsTo8 (a + 1#64) (v.extractLsb' 8 8) ∗
  pointsTo8 (a + 2#64) (v.extractLsb' 16 8) ∗
  pointsTo8 (a + 3#64) (v.extractLsb' 24 8) ∗
  pointsTo8 (a + 4#64) (v.extractLsb' 32 8) ∗
  pointsTo8 (a + 5#64) (v.extractLsb' 40 8) ∗
  pointsTo8 (a + 6#64) (v.extractLsb' 48 8) ∗
  pointsTo8 (a + 7#64) (v.extractLsb' 56 8)

/-- 128-bit little-endian points-to assertion (`a ↦₁₂₈ v`). -/
def pointsTo128 (a : BitVec 64) (v : BitVec 128) : SepProp :=
  pointsTo64 a (v.extractLsb' 0 64) ∗ pointsTo64 (a + 8#64) (v.extractLsb' 64 64)

/-- Contiguous 64-bit little-endian word-list points-to assertion (`a ↦₆₄* ws`). -/
def pointsToWords64 (a : BitVec 64) : List (BitVec 64) → SepProp
  | []      => emp
  | w :: ws => pointsTo64 a w ∗ pointsToWords64 (a + 8#64) ws

infix:70 " ↦₈ " => pointsTo8
infix:70 " ↦ₛ " => pointsToBytes
infix:70 " ↦₁₆ " => pointsTo16
infix:70 " ↦₃₂ " => pointsTo32
infix:70 " ↦₆₄ " => pointsTo64
infix:70 " ↦₁₂₈ " => pointsTo128
infix:70 " ↦₆₄* " => pointsToWords64

/-- 16-bit little-endian read-only points-to assertion (`a ↦₁₆ᵣ v`). -/
def pointsTo16RO (a : BitVec 64) (v : BitVec 16) : SepProp :=
  pointsTo8RO (a + 0#64) (v.extractLsb' 0 8) ∗
  pointsTo8RO (a + 1#64) (v.extractLsb' 8 8)

/-- 32-bit little-endian read-only points-to assertion (`a ↦₃₂ᵣ v`). -/
def pointsTo32RO (a : BitVec 64) (v : BitVec 32) : SepProp :=
  pointsTo8RO (a + 0#64) (v.extractLsb' 0 8) ∗
  pointsTo8RO (a + 1#64) (v.extractLsb' 8 8) ∗
  pointsTo8RO (a + 2#64) (v.extractLsb' 16 8) ∗
  pointsTo8RO (a + 3#64) (v.extractLsb' 24 8)

/-- 64-bit little-endian read-only points-to assertion (`a ↦₆₄ᵣ v`). -/
def pointsTo64RO (a : BitVec 64) (v : BitVec 64) : SepProp :=
  pointsTo8RO (a + 0#64) (v.extractLsb' 0 8) ∗
  pointsTo8RO (a + 1#64) (v.extractLsb' 8 8) ∗
  pointsTo8RO (a + 2#64) (v.extractLsb' 16 8) ∗
  pointsTo8RO (a + 3#64) (v.extractLsb' 24 8) ∗
  pointsTo8RO (a + 4#64) (v.extractLsb' 32 8) ∗
  pointsTo8RO (a + 5#64) (v.extractLsb' 40 8) ∗
  pointsTo8RO (a + 6#64) (v.extractLsb' 48 8) ∗
  pointsTo8RO (a + 7#64) (v.extractLsb' 56 8)

/-- 128-bit little-endian read-only points-to assertion (`a ↦₁₂₈ᵣ v`). -/
def pointsTo128RO (a : BitVec 64) (v : BitVec 128) : SepProp :=
  pointsTo64RO a (v.extractLsb' 0 64) ∗ pointsTo64RO (a + 8#64) (v.extractLsb' 64 64)

/-- Contiguous 64-bit little-endian word-list read-only points-to assertion (`a ↦₆₄ᵣ* ws`). -/
def pointsToWords64RO (a : BitVec 64) : List (BitVec 64) → SepProp
  | []      => emp
  | w :: ws => pointsTo64RO a w ∗ pointsToWords64RO (a + 8#64) ws

infix:70 " ↦₈ᵣ " => pointsTo8RO
infix:70 " ↦ᵣ " => pointsToBytesRO
infix:70 " ↦₁₆ᵣ " => pointsTo16RO
infix:70 " ↦₃₂ᵣ " => pointsTo32RO
infix:70 " ↦₆₄ᵣ " => pointsTo64RO
infix:70 " ↦₁₂₈ᵣ " => pointsTo128RO
infix:70 " ↦₆₄ᵣ* " => pointsToWords64RO

infix:70 " ↦₈ₙ " => pointsTo8ProtNone
infix:70 " ↦ₙ " => pointsToBytesProtNone

/-- 16-bit lazy-free read-write points-to assertion (`a ↦₁₆ₗ`). -/
def pointsTo16Lazy (a : BitVec 64) : SepProp :=
  pointsTo8Lazy (a + 0#64) ∗
  pointsTo8Lazy (a + 1#64)

/-- 32-bit lazy-free read-write points-to assertion (`a ↦₃₂ₗ`). -/
def pointsTo32Lazy (a : BitVec 64) : SepProp :=
  pointsTo8Lazy (a + 0#64) ∗
  pointsTo8Lazy (a + 1#64) ∗
  pointsTo8Lazy (a + 2#64) ∗
  pointsTo8Lazy (a + 3#64)

/-- 64-bit lazy-free read-write points-to assertion (`a ↦₆₄ₗ`). -/
def pointsTo64Lazy (a : BitVec 64) : SepProp :=
  pointsTo8Lazy (a + 0#64) ∗
  pointsTo8Lazy (a + 1#64) ∗
  pointsTo8Lazy (a + 2#64) ∗
  pointsTo8Lazy (a + 3#64) ∗
  pointsTo8Lazy (a + 4#64) ∗
  pointsTo8Lazy (a + 5#64) ∗
  pointsTo8Lazy (a + 6#64) ∗
  pointsTo8Lazy (a + 7#64)

/-- 128-bit lazy-free read-write points-to assertion (`a ↦₁₂₈ₗ`). -/
def pointsTo128Lazy (a : BitVec 64) : SepProp :=
  pointsTo64Lazy a ∗ pointsTo64Lazy (a + 8#64)

/-- Alias for `memRegionLazy` (`len`-byte lazy-free read-write region `[base, base + len)`). -/
abbrev memLazy (base : BitVec 64) (len : Nat) : SepProp :=
  memRegionLazy base len

postfix:70 " ↦₈ₗ" => pointsTo8Lazy
postfix:70 " ↦₁₆ₗ" => pointsTo16Lazy
postfix:70 " ↦₃₂ₗ" => pointsTo32Lazy
postfix:70 " ↦₆₄ₗ" => pointsTo64Lazy
postfix:70 " ↦₁₂₈ₗ" => pointsTo128Lazy
postfix:70 " ↦ₗ" => pointsTo8Lazy

/-- Separation logic assertion owning a `len`-byte downward stack frame
    `[s.sp - len, s.sp)` below `s.sp` with existential memory contents. -/
abbrev stackFrame (s : State) (len : Nat) : SepProp :=
  memRegion (s.sp - BitVec.ofNat 64 len) len

/-- Separation logic assertion for a 16-byte downward stack frame (`[sp - 16, sp)`),
    owning the two 8-byte stack slots `sp - 16` and `sp - 8` with existential values. -/
def stackFrame16At (sp : BitVec 64) : SepProp :=
  ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64,
    ((sp - 16#64) ↦₆₄ v0) ∗ ((sp - 8#64) ↦₆₄ v1)

/-- Separation logic assertion for a 16-byte downward stack frame (`[s.sp - 16, s.sp)`). -/
abbrev stackFrame16 (s : State) : SepProp :=
  stackFrame16At s.sp

/-- Separation logic assertion for a 32-byte downward stack frame (`[sp - 32, sp)`),
    owning the four 8-byte stack slots `sp - 32`, `sp - 24`, `sp - 16`, and `sp - 8`
    with existential values. -/
def stackFrame32At (sp : BitVec 64) : SepProp :=
  ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
    ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
    ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3)

/-- Separation logic assertion for a 32-byte downward stack frame (`[s.sp - 32, s.sp)`). -/
abbrev stackFrame32 (s : State) : SepProp :=
  stackFrame32At s.sp

/-- Prepend `n` downward 8-byte stack slots ending at `sp - k * 8` using continuation `cont`,
    placing all `∃∗` quantifiers in prenex position and associating `∗` to the right:
    `∃∗ v₀ ⋯ v_{n-1}, cont ((sp - (k + n) * 8) ↦₆₄ v₀ ∗ ⋯ ∗ (sp - (k + 1) * 8) ↦₆₄ v_{n-1})`. -/
def stackFrameSlotsCont (sp : BitVec 64) (k : Nat) : Nat → (SepProp → SepProp) → SepProp
  | 0, cont => cont emp
  | 1, cont =>
    ∃∗ v : BitVec 64, cont ((sp - BitVec.ofNat 64 ((k + 1) * 8)) ↦₆₄ v)
  | n + 2, cont =>
    ∃∗ v : BitVec 64,
      stackFrameSlotsCont sp k (n + 1)
        (fun rest => cont (((sp - BitVec.ofNat 64 ((k + n + 2) * 8)) ↦₆₄ v) ∗ rest))

/-- Existentially quantified 8-byte stack slots for `n` downward slots ending at `sp - k * 8`:
    `∃∗ v₀ ⋯ v_{n-1}, ((sp - (k + n) * 8) ↦₆₄ v₀ ∗ ⋯ ∗ (sp - (k + 1) * 8) ↦₆₄ v_{n-1})`. -/
def stackFrameSlotsFrom (sp : BitVec 64) (k n : Nat) : SepProp :=
  stackFrameSlotsCont sp k n (fun P => P)

/-- Separation logic assertion for an `n`-byte downward stack frame (`[sp - n, sp)`):
    - `emp` when `n = 0`,
    - `n / 8` existentially quantified 8-byte stack slots when `n > 0` and `n % 8 = 0`,
    - `memRegion (sp - BitVec.ofNat 64 n) n` otherwise. -/
def stackFrameAt (sp : BitVec 64) (n : Nat) : SepProp :=
  if n == 0 then emp
  else if n % 8 == 0 then stackFrameSlotsFrom sp 0 (n / 8)
  else memRegion (sp - BitVec.ofNat 64 n) n

/-! ## Abstract Heap Allocator Interfaces (`Allocator`, `AllocatorOom`) -/

/-- Abstract heap allocator interface: an allocator state assertion `pool : SepProp`, a
    per-allocation ownership token `live : BitVec 64 → Nat → SepProp` parameterized by pointer
    and byte size, and a proof `noWrap` that every live block fits in the 64-bit address space
    without wrapping (`p.toNat + sz ≤ 2 ^ 64`). -/
protected structure Allocator where
  /-- Aggregate allocator state assertion (free lists, arenas, metadata). -/
  pool : SepProp
  /-- Per-allocation ownership token for a block at `p` of `sz` bytes. -/
  live : BitVec 64 → Nat → SepProp
  /-- Every live block fits in the 64-bit address space without wrapping (`p.toNat + sz ≤ 2 ^ 64`). -/
  noWrap : ∀ (p : BitVec 64) (sz : Nat), live p sz ⊢ ⌜p.toNat + sz ≤ 2 ^ 64⌝ ∗ live p sz

/-- Extended allocator interface equipped with an OOM-refusal state `pool : Bool → SepProp`:
    `pool false` is the healthy allocator invariant prior to any null return;
    `pool true` witnesses that an allocator call refused (`ret = 0`). -/
protected structure AllocatorOom where
  /-- Aggregate allocator state assertion indexed by whether OOM refusal has occurred. -/
  pool : Bool → SepProp
  /-- Per-allocation ownership token for a block at `p` of `sz` bytes. -/
  live : BitVec 64 → Nat → SepProp
  /-- Every live block fits in the 64-bit address space without wrapping (`p.toNat + sz ≤ 2 ^ 64`). -/
  noWrap : ∀ (p : BitVec 64) (sz : Nat), live p sz ⊢ ⌜p.toNat + sz ≤ 2 ^ 64⌝ ∗ live p sz

/-- Underlying base `Allocator` prior to any OOM refusal (`pool false`). -/
def AllocatorOom.toAllocator (A : Arm64.AllocatorOom) : Arm64.Allocator where
  pool := A.pool false
  live := A.live
  noWrap := A.noWrap

/-- Lift a standard `Allocator` to `AllocatorOom` with `pool _ := A.pool`. -/
def Allocator.toAllocatorOom (A : Arm64.Allocator) : Arm64.AllocatorOom where
  pool := fun _ => A.pool
  live := A.live
  noWrap := A.noWrap

end -- @[expose] public section

end Arm64


