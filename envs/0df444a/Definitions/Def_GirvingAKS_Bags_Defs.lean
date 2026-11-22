-- Prove2me | Definitions.Def_GirvingAKS_Bags_Defs
-- name    : GirvingAKS_Bags_Defs
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:30:29.799677+00:00
-- url     : https://prove2.me/theorems/5ad632b4-7a2f-47c5-81cf-af253e97355c
-- title:
--   AKS sorting networks (Seiferas port) — Bag Definitions for Separator-Based Sorting
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Bags/Defs.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** Defines the binary bag tree structure for the Seiferas (2009) separator-based sorting network proof (Sections 2–5).
--
--   The primary objects in this formalization are **registers** (wire positions, `Fin (2^k)`), not values. A `Placement` says which registers each bag owns. Definitions that need to know a register's value use a permutation `perm : Fin (2^k) → Fin (2^k)` to look up the sorted rank. This keeps the bag structure purely positional: bags own registers, and the permutation tells us what value each register holds.
--
--   Key definitions:
--
--   - `Bag`: a bag in the binary tree (level + horizontal coordinate)
--   - `Placement`: assignment of registers to bags (with disjointness/completeness)
--   - `bagSize`, `nativeBagIdx`: bag structure in the binary tree
--   - `Bag.Native`, `Bag.Strange`: whether an item is native/strange at a bag
--
--   All definitions validated by Rust simulation (`rust/test-bags.rs`):
--
--   - Invariant holds with adversarial separator for n = 8..16384
--   - j-stranger monotonicity confirmed: (j+1)-strange → j-strange
--   - Parity convention: (t + level) % 2 ≠ 0 → empty
--
--   Parameterized by `k : ℕ` where the number of wires is `2^k`.
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Bags/Defs.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Sort_Defs

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Bags/Defs.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Bag Definitions for Separator-Based Sorting

  Defines the binary bag tree structure for the Seiferas (2009)
  separator-based sorting network proof (Sections 2–5).

  ## Register-first convention

  The primary objects in this formalization are **registers** (wire positions,
  `Fin (2^k)`), not values. A `Placement` says which registers each bag owns.
  Definitions that need to know a register's value use a permutation
  `perm : Fin (2^k) → Fin (2^k)` to look up the sorted rank. This keeps
  the bag structure purely positional: bags own registers, and the
  permutation tells us what value each register holds.

  Key definitions:
  - `Bag`: a bag in the binary tree (level + horizontal coordinate)
  - `Placement`: assignment of registers to bags (with disjointness/completeness)
  - `bagSize`, `nativeBagIdx`: bag structure in the binary tree
  - `Bag.Native`, `Bag.Strange`: whether an item is native/strange at a bag

  All definitions validated by Rust simulation (`rust/test-bags.rs`):
  - Invariant holds with adversarial separator for n = 8..16384
  - j-stranger monotonicity confirmed: (j+1)-strange → j-strange
  - Parity convention: (t + level) % 2 ≠ 0 → empty

  Parameterized by `k : ℕ` where the number of wires is `2^k`.
-/


section


open Finset

/-! **Bag Tree Structure** -/

/-- Size of each bag's native interval at a given level: `2^k / 2^level`.
    At level 0 (root): `bagSize k 0 = 2^k`. At level `ℓ`: each bag covers
    `2^k / 2^ℓ` items. -/
def bagSize (k level : ℕ) : ℕ := 2 ^ k / 2 ^ level

/-- The bag index that an item with sorted rank `r` is native to at a given
    level. `nativeBagIdx k level r = r / (2^k / 2^level)`. -/
def nativeBagIdx (k level : ℕ) (r : ℕ) : ℕ := r / bagSize k level

/-! **Bag Index** -/

/-- A bag in the binary tree on `2^k` items, at level `l` and horizontal
    coordinate `x`. The constraint `l ≤ k` ensures the level is within
    the tree (at level `k`, bags have size 1). The constraint `x < 2 ^ l`
    ensures the bag index is valid (there are `2^l` bags at level `l`). -/
@[ext]
structure Bag (k : ℕ) where
  l : ℕ
  x : ℕ
  hl : l ≤ k
  hx : x < 2 ^ l
  deriving DecidableEq

variable {k : ℕ}

/-- Native interval size for this bag: `2^k / 2^l`. -/
def Bag.size (b : Bag k) : ℕ := bagSize k b.l

/-- Parent bag (one level up). -/
def Bag.parent (b : Bag k) : Bag k :=
  ⟨b.l - 1, b.x / 2, Nat.le_trans (Nat.sub_le b.l 1) b.hl, by
    by_cases hl0 : b.l = 0
    · have := b.hx; simp only [hl0, Nat.zero_sub, pow_zero] at this ⊢; omega
    · exact Nat.div_lt_of_lt_mul (by
        have h1 := b.hx
        have h2 : 2 * 2 ^ (b.l - 1) = 2 ^ b.l := by
          rw [Nat.mul_comm, ← pow_succ, Nat.sub_add_cancel (by omega)]
        omega)⟩

/-- Left child bag (one level down). -/
def Bag.left (b : Bag k) (h : b.l < k := by omega) : Bag k :=
  ⟨b.l + 1, 2 * b.x, by omega, by have := b.hx; rw [pow_succ]; omega⟩

/-- Right child bag (one level down). -/
def Bag.right (b : Bag k) (h : b.l < k := by omega) : Bag k :=
  ⟨b.l + 1, 2 * b.x + 1, by omega, by have := b.hx; rw [pow_succ]; omega⟩

/-- The root bag (level 0, index 0). -/
def Bag.root (k : ℕ) : Bag k := ⟨0, 0, Nat.zero_le k, by omega⟩

/-- Lower bound of the native rank interval: `b.x * b.size`. -/
def Bag.lo (b : Bag k) : ℕ := b.x * b.size

/-- Upper bound (exclusive) of the native rank interval: `(b.x + 1) * b.size`. -/
def Bag.hi (b : Bag k) : ℕ := (b.x + 1) * b.size

/-! **Placement** -/

/-- Assignment of registers to bags, with proof that every wire belongs to
    exactly one bag. The function `regs` maps each bag to its set of
    registers (wire positions). -/
structure Placement (k : ℕ) where
  /-- Which registers each bag owns. -/
  regs : Bag k → Finset (Fin (2 ^ k))
  /-- Each wire belongs to at most one bag. -/
  disjoint : ∀ (a b : Bag k), a ≠ b → Disjoint (regs a) (regs b)
  /-- Every wire is accounted for. -/
  complete : ∀ (i : Fin (2 ^ k)), ∃ (b : Bag k), i ∈ regs b

/-! **Ancestry, Nativeness, Strangeness** -/

/-- The ancestor of bag `b` at `j` levels up. `b.ancestor 0 = b`,
    `b.ancestor 1 = b.parent`, etc. -/
def Bag.ancestor (b : Bag k) (j : ℕ) : Bag k :=
  ⟨b.l - j, b.x / 2 ^ j, Nat.le_trans (Nat.sub_le b.l j) b.hl, by
    by_cases hjl : j ≤ b.l
    · exact Nat.div_lt_of_lt_mul (by
        rw [← pow_add, show j + (b.l - j) = b.l from by omega]; exact b.hx)
    · push_neg at hjl
      rw [Nat.sub_eq_zero_of_le hjl.le, pow_zero]
      have h1 : b.x < 2 ^ j :=
        Nat.lt_of_lt_of_le b.hx (Nat.pow_le_pow_right (by omega) hjl.le)
      rw [Nat.div_eq_of_lt h1]; omega⟩

/-- Register `r` is native to bag `b` if its sorted rank (via `perm`) maps
    to `b`'s interval at level `b.l`. -/
def Bag.Native (b : Bag k) (r : Fin (2 ^ k)) (perm : Fin (2 ^ k) → Fin (2 ^ k)) : Prop :=
  nativeBagIdx k b.l (perm r).val = b.x

instance Bag.instDecidableNative (b : Bag k) (r : Fin (2 ^ k))
    (perm : Fin (2 ^ k) → Fin (2 ^ k)) : Decidable (b.Native r perm) :=
  inferInstanceAs (Decidable (nativeBagIdx k b.l (perm r).val = b.x))

/-- Register `r` is `j`-strange at bag `b` if its native path has diverged
    from `b`'s ancestry at least `j` steps from the leaves
    (Seiferas 2009, Section 3).

    - `j = 0`: trivially true (all items are 0-strange)
    - `j = 1`: not native to this bag
    - `j = m+1`: not native to `b.ancestor m`

    Key property: `(j+1)`-strange → `j`-strange. -/
def Bag.Strange (b : Bag k) (j : ℕ) (r : Fin (2 ^ k)) (perm : Fin (2 ^ k) → Fin (2 ^ k)) : Prop :=
  j = 0 ∨ ¬(b.ancestor (j - 1)).Native r perm

instance Bag.instDecidableStrange (b : Bag k) (j : ℕ) (r : Fin (2 ^ k))
    (perm : Fin (2 ^ k) → Fin (2 ^ k)) : Decidable (b.Strange j r perm) :=
  inferInstanceAs (Decidable (j = 0 ∨ ¬(b.ancestor (j - 1)).Native r perm))

/-! **Stranger Count** -/

/-- Count of j-strangers in bag `b` among registers `S`.
    Uses `Bag.Strange`: for j=0 all items are strange (count = card),
    for j ≥ 1 counts items not native to `b.ancestor (j-1)`. -/
def Bag.strangers (b : Bag k) (j : ℕ) (perm : Fin (2 ^ k) → Fin (2 ^ k))
    (S : Finset (Fin (2 ^ k))) : ℕ :=
  (S.filter (fun r ↦ b.Strange j r perm)).card

/-- Subset monotonicity. -/
theorem Bag.strangers_mono (b : Bag k) (j : ℕ) (perm : Fin (2 ^ k) → Fin (2 ^ k))
    {S T : Finset (Fin (2 ^ k))} (h : S ⊆ T) :
    b.strangers j perm S ≤ b.strangers j perm T :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

/-- Union bound. -/
theorem Bag.strangers_union_le (b : Bag k) (j : ℕ) (perm : Fin (2 ^ k) → Fin (2 ^ k))
    (S T : Finset (Fin (2 ^ k))) :
    b.strangers j perm (S ∪ T) ≤ b.strangers j perm S + b.strangers j perm T := by
  simp only [Bag.strangers, Finset.filter_union]
  exact Finset.card_union_le _ _

/-- Empty set has 0 strangers. -/
@[simp] theorem Bag.strangers_empty (b : Bag k) (j : ℕ)
    (perm : Fin (2 ^ k) → Fin (2 ^ k)) :
    b.strangers j perm ∅ = 0 := by
  simp [Bag.strangers]

/-- Stranger count is at most the set size. -/
theorem Bag.strangers_le_card (b : Bag k) (j : ℕ) (perm : Fin (2 ^ k) → Fin (2 ^ k))
    (S : Finset (Fin (2 ^ k))) :
    b.strangers j perm S ≤ S.card :=
  Finset.card_filter_le _ _

/-! **Basic Lemmas**

Raw `bagSize`/`nativeBagIdx` versions. Prefer the `Bag.*` API below. -/

@[simp] theorem bagSize_zero (k : ℕ) : bagSize k 0 = 2 ^ k := by
  simp [bagSize]

theorem bagSize_pos {k level : ℕ} (h : level ≤ k) : 0 < bagSize k level := by
  exact Nat.div_pos (Nat.pow_le_pow_right (by omega) h) (pow_pos (by omega) level)

@[simp] theorem nativeBagIdx_root {k r : ℕ} (hr : r < 2 ^ k) :
    nativeBagIdx k 0 r = 0 := by
  simp only [nativeBagIdx, bagSize_zero]
  exact Nat.div_eq_of_lt hr

/-- `bagSize k (ℓ+1) * 2 = bagSize k ℓ`: each level doubles the bag size. -/
theorem bagSize_succ_mul_two {k ℓ : ℕ} (h : ℓ + 1 ≤ k) :
    bagSize k (ℓ + 1) * 2 = bagSize k ℓ := by
  simp only [bagSize]
  rw [Nat.pow_div h (by positivity), Nat.pow_div (by omega) (by positivity), ← pow_succ]
  congr 1; omega

/-- `nativeBagIdx k (ℓ+1) r / 2 = nativeBagIdx k ℓ r`: going up a level divides
    the bag index by 2. -/
theorem nativeBagIdx_div_two {k ℓ r : ℕ} (h : ℓ + 1 ≤ k) :
    nativeBagIdx k (ℓ + 1) r / 2 = nativeBagIdx k ℓ r := by
  simp only [nativeBagIdx]
  rw [Nat.div_div_eq_div_mul, bagSize_succ_mul_two h]

/-- `idx / 2^(j-1) / 2 = idx / 2^j` for `j ≥ 1`. -/
theorem div_pow_pred_div_two {idx j : ℕ} (hj : 1 ≤ j) :
    idx / 2 ^ (j - 1) / 2 = idx / 2 ^ j := by
  rw [Nat.div_div_eq_div_mul, ← pow_succ, Nat.sub_add_cancel hj]

/-- `idx / 2 / 2^(j-1) = idx / 2^j` for `j ≥ 1`. -/
theorem div_two_div_pow_pred {idx j : ℕ} (hj : 1 ≤ j) :
    idx / 2 / 2 ^ (j - 1) = idx / 2 ^ j := by
  rw [Nat.div_div_eq_div_mul, mul_comm, ← pow_succ, Nat.sub_add_cancel hj]

/-! **Bag API Lemmas** -/

theorem Bag.size_pos (b : Bag k) : 0 < b.size :=
  bagSize_pos b.hl

@[simp] theorem Bag.size_root : (Bag.root k).size = 2 ^ k :=
  bagSize_zero k

theorem Bag.size_left (b : Bag k) (h : b.l < k := by omega) :
    (b.left h).size * 2 = b.size :=
  bagSize_succ_mul_two (by omega)

theorem Bag.size_right (b : Bag k) (h : b.l < k := by omega) :
    (b.right h).size * 2 = b.size :=
  bagSize_succ_mul_two (by omega)

theorem Bag.hi_eq_lo_add_size (b : Bag k) : b.hi = b.lo + b.size := by
  simp [Bag.hi, Bag.lo, Nat.add_mul]

theorem Bag.lo_lt_hi (b : Bag k) : b.lo < b.hi := by
  simp only [Bag.hi, Bag.lo, Nat.add_mul, Nat.one_mul]
  exact Nat.lt_add_of_pos_right b.size_pos

/-! **Child interval nesting** -/

/-- Left child's interval starts at the parent's lo. -/
theorem Bag.lo_left_eq (b : Bag k) (h : b.l < k) :
    (b.left h).lo = b.lo := by
  simp only [Bag.lo, Bag.size]
  set s := bagSize k (b.l + 1)
  show 2 * b.x * s = b.x * bagSize k b.l
  rw [← bagSize_succ_mul_two (show b.l + 1 ≤ k by omega)]
  ring

/-- Left child's hi ≤ parent's hi. -/
theorem Bag.hi_left_le (b : Bag k) (h : b.l < k) :
    (b.left h).hi ≤ b.hi := by
  simp only [Bag.hi, Bag.size]
  set s := bagSize k (b.l + 1)
  show (2 * b.x + 1) * s ≤ (b.x + 1) * bagSize k b.l
  rw [← bagSize_succ_mul_two (show b.l + 1 ≤ k by omega)]
  calc (2 * b.x + 1) * s
      ≤ (2 * b.x + 2) * s := Nat.mul_le_mul_right s (by omega)
    _ = (b.x + 1) * (s * 2) := by ring

/-- Right child's lo ≥ parent's lo. -/
theorem Bag.lo_right_ge (b : Bag k) (h : b.l < k) :
    b.lo ≤ (b.right h).lo := by
  simp only [Bag.lo, Bag.size]
  set s := bagSize k (b.l + 1)
  show b.x * bagSize k b.l ≤ (2 * b.x + 1) * s
  rw [← bagSize_succ_mul_two (show b.l + 1 ≤ k by omega)]
  calc b.x * (s * 2)
      = 2 * b.x * s := by ring
    _ ≤ (2 * b.x + 1) * s := Nat.mul_le_mul_right s (by omega)

/-- Right child's interval ends at the parent's hi. -/
theorem Bag.hi_right_eq (b : Bag k) (h : b.l < k) :
    (b.right h).hi = b.hi := by
  simp only [Bag.hi, Bag.size]
  set s := bagSize k (b.l + 1)
  show (2 * b.x + 1 + 1) * s = (b.x + 1) * bagSize k b.l
  rw [← bagSize_succ_mul_two (show b.l + 1 ≤ k by omega)]
  ring

/-- Register `r` is native to `b` iff its sorted rank lies in `[b.lo, b.hi)`. -/
theorem Bag.native_iff (b : Bag k) (r : Fin (2 ^ k)) (perm : Fin (2 ^ k) → Fin (2 ^ k)) :
    b.Native r perm ↔ b.lo ≤ (perm r).val ∧ (perm r).val < b.hi := by
  simp only [Bag.Native, Bag.lo, Bag.hi, Bag.size, nativeBagIdx]
  constructor
  · intro h
    constructor
    · rw [← h]; exact Nat.div_mul_le_self _ _
    · rw [← h, Nat.add_mul, Nat.one_mul]; exact Nat.lt_div_mul_add (bagSize_pos b.hl)
  · intro ⟨hlo, hhi⟩
    have hpos := bagSize_pos b.hl
    have h1 : b.x ≤ (perm r).val / bagSize k b.l := (Nat.le_div_iff_mul_le hpos).mpr hlo
    have h2 : (perm r).val / bagSize k b.l < b.x + 1 := (Nat.div_lt_iff_lt_mul hpos).mpr hhi
    omega

/-- All registers are native to the root bag. -/
theorem Bag.native_root (r : Fin (2 ^ k)) (perm : Fin (2 ^ k) → Fin (2 ^ k)) :
    (Bag.root k).Native r perm := by
  simp [Bag.Native, Bag.root, nativeBagIdx_root (perm r).isLt]

/-! **Bag Extensionality and Tree Structure** -/

/-- A non-root bag with even `x` is the left child of its parent. -/
theorem Bag.parent_left_eq (c : Bag k) (hcl : 1 ≤ c.l) (heven : c.x % 2 = 0)
    (h : c.parent.l < k := by have := c.hl; unfold Bag.parent; simp; omega) :
    c.parent.left h = c :=
  Bag.ext (by show c.l - 1 + 1 = c.l; omega) (by show 2 * (c.x / 2) = c.x; omega)

/-- A non-root bag with odd `x` is the right child of its parent. -/
theorem Bag.parent_right_eq (c : Bag k) (hcl : 1 ≤ c.l) (hodd : c.x % 2 ≠ 0)
    (h : c.parent.l < k := by have := c.hl; unfold Bag.parent; simp; omega) :
    c.parent.right h = c :=
  Bag.ext (by show c.l - 1 + 1 = c.l; omega) (by show 2 * (c.x / 2) + 1 = c.x; omega)

/-- Left child's parent is the original bag. -/
theorem Bag.left_parent_eq (b : Bag k) (h : b.l < k) : (b.left h).parent = b :=
  Bag.ext (by show b.l + 1 - 1 = b.l; omega) (by show 2 * b.x / 2 = b.x; omega)

/-- Left child has even index. -/
theorem Bag.left_x_mod (b : Bag k) (h : b.l < k) : (b.left h).x % 2 = 0 := by
  show (2 * b.x) % 2 = 0; omega

/-- Right child's parent is the original bag. -/
theorem Bag.right_parent_eq (b : Bag k) (h : b.l < k) : (b.right h).parent = b :=
  Bag.ext (by show b.l + 1 - 1 = b.l; omega) (by show (2 * b.x + 1) / 2 = b.x; omega)

/-- Right child has odd index. -/
theorem Bag.right_x_mod (b : Bag k) (h : b.l < k) : (b.right h).x % 2 ≠ 0 := by
  show (2 * b.x + 1) % 2 ≠ 0; omega

/-! **Bag Enumeration** -/

/-- All bags in a depth-`k` tree: for each level `l ∈ [0, k]`, bags with
    index `x ∈ [0, 2^l)`. -/
def allBags (k : ℕ) : List (Bag k) :=
  ((List.range (k + 1)).attach).flatMap fun ⟨l, hl⟩ ↦
    let hl' : l ≤ k := by rw [List.mem_range] at hl; omega
    ((List.range (2 ^ l)).attach).map fun ⟨x, hx⟩ ↦
      ⟨l, x, hl', by rwa [List.mem_range] at hx⟩

/-- Every bag is in `allBags k`. -/
theorem Bag.mem_allBags (b : Bag k) : b ∈ allBags k := by
  simp only [allBags, List.mem_flatMap, List.mem_attach, true_and, List.mem_map,
    List.mem_range, Subtype.exists]
  exact ⟨b.l, by have := b.hl; omega, b.x, b.hx, by ext <;> rfl⟩

/-- `allBags k` has no duplicate entries. -/
theorem allBags_nodup : (allBags k).Nodup := by
  unfold allBags
  rw [List.nodup_flatMap]
  constructor
  · intro ⟨l, hl⟩ _
    apply List.Nodup.map
    · intro ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩ heq
      exact Subtype.ext (congrArg Bag.x heq)
    · exact List.nodup_range.attach
  · apply List.nodup_range.attach.pairwise_of_forall_ne
    intro ⟨l₁, hl₁⟩ _ ⟨l₂, hl₂⟩ _ hne
    rw [Function.onFun, List.Disjoint]
    intro b hb₁ hb₂
    simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists] at hb₁ hb₂
    obtain ⟨x₁, _, rfl⟩ := hb₁
    obtain ⟨x₂, _, heq⟩ := hb₂
    have := congrArg Bag.l heq
    simp at this
    exact hne (Subtype.ext this.symm)

/-! **Ancestry Lemmas** -/

/-- If `r` is native to `b`, then `r` is native to `b.parent`. -/
theorem Bag.Native.parent {b : Bag k} {r : Fin (2 ^ k)} {perm : Fin (2 ^ k) → Fin (2 ^ k)}
    (h : b.Native r perm) (hl : 1 ≤ b.l) :
    b.parent.Native r perm := by
  simp only [Bag.Native, Bag.parent] at *
  show nativeBagIdx k (b.l - 1) (perm r).val = b.x / 2
  have hlk : (b.l - 1) + 1 ≤ k := by have := b.hl; omega
  have hbl : (b.l - 1) + 1 = b.l := by omega
  rw [← nativeBagIdx_div_two hlk, hbl, h]

/-! **Stranger Level Shift** -/

/-- Level shift: j-strangers at parent = (j+1)-strangers at child.
    For j ≥ 1 and b.l ≥ 1. -/
theorem Bag.strangers_parent_eq (b : Bag k) (j : ℕ) (hj : 1 ≤ j) (_ : 1 ≤ b.l)
    (perm : Fin (2 ^ k) → Fin (2 ^ k)) (S : Finset (Fin (2 ^ k))) :
    b.parent.strangers j perm S = b.strangers (j + 1) perm S := by
  simp only [Bag.strangers]
  congr 1; ext r
  simp only [Finset.mem_filter]
  constructor
  · intro ⟨hmem, hns⟩; exact ⟨hmem, by
      show b.Strange (j + 1) r perm
      simp only [Bag.Strange, show j + 1 ≠ 0 by omega, false_or, show j + 1 - 1 = j by omega]
      have hns' : ¬(b.parent.ancestor (j - 1)).Native r perm := by
        simp only [Bag.Strange, show j ≠ 0 by omega, false_or] at hns; exact hns
      have heq : b.parent.ancestor (j - 1) = b.ancestor j := by
        ext
        · show b.l - 1 - (j - 1) = b.l - j; omega
        · show (b.x / 2) / 2 ^ (j - 1) = b.x / 2 ^ j
          exact div_two_div_pow_pred hj
      rwa [← heq]⟩
  · intro ⟨hmem, hns⟩; exact ⟨hmem, by
      show b.parent.Strange j r perm
      simp only [Bag.Strange, show j ≠ 0 by omega, false_or]
      have hns' : ¬(b.ancestor j).Native r perm := by
        simp only [Bag.Strange, show j + 1 ≠ 0 by omega, false_or, show j + 1 - 1 = j by omega] at hns
        exact hns
      have heq : b.parent.ancestor (j - 1) = b.ancestor j := by
        ext
        · show b.l - 1 - (j - 1) = b.l - j; omega
        · show (b.x / 2) / 2 ^ (j - 1) = b.x / 2 ^ j
          exact div_two_div_pow_pred hj
      rwa [heq]⟩

/-! **Sibling Structure** -/

/-- The sibling of bag `b` (the other child of b's parent).
    For a left child (even x), returns the right sibling.
    For a right child (odd x), returns the left sibling. -/
def Bag.sibling (b : Bag k) (hl : 1 ≤ b.l) : Bag k :=
  let hp : b.parent.l < k := by unfold Bag.parent; simp only; have := b.hl; omega
  if b.x % 2 = 0 then b.parent.right hp else b.parent.left hp

/-- Sibling's parent equals b's parent. -/
theorem Bag.sibling_parent_eq (b : Bag k) (hl : 1 ≤ b.l) :
    (b.sibling hl).parent = b.parent := by
  simp only [Bag.sibling]
  split_ifs with heven
  · exact Bag.right_parent_eq _ _
  · exact Bag.left_parent_eq _ _

/-- Sibling is at the same level as b. -/
theorem Bag.sibling_level_eq (b : Bag k) (hl : 1 ≤ b.l) :
    (b.sibling hl).l = b.l := by
  simp only [Bag.sibling, Bag.left, Bag.right, Bag.parent]
  split_ifs <;> change b.l - 1 + 1 = b.l <;> omega

/-- Sibling is distinct from b. -/
theorem Bag.sibling_ne (b : Bag k) (hl : 1 ≤ b.l) :
    b.sibling hl ≠ b := by
  intro heq
  have hx := congr_arg Bag.x heq
  simp only [Bag.sibling, Bag.left, Bag.right, Bag.parent] at hx
  split_ifs at hx with heven
  · change 2 * (b.x / 2) + 1 = b.x at hx; omega
  · change 2 * (b.x / 2) = b.x at hx; omega

/-- If b is a left child, its sibling is the right child of parent. -/
theorem Bag.sibling_of_left (b : Bag k) (hl : 1 ≤ b.l) (heven : b.x % 2 = 0) :
    b.sibling hl = b.parent.right (by unfold Bag.parent; simp; have := b.hl; omega) := by
  simp only [Bag.sibling, if_pos heven]

/-- If b is a right child, its sibling is the left child of parent. -/
theorem Bag.sibling_of_right (b : Bag k) (hl : 1 ≤ b.l) (hodd : b.x % 2 ≠ 0) :
    b.sibling hl = b.parent.left (by unfold Bag.parent; simp; have := b.hl; omega) := by
  simp only [Bag.sibling, if_neg hodd]

/-- Sibling's x-coordinate when b is a left child (even x). -/
theorem Bag.sibling_x_even (b : Bag k) (hl : 1 ≤ b.l) (heven : b.x % 2 = 0) :
    (b.sibling hl).x = b.x + 1 := by
  simp only [Bag.sibling, if_pos heven, Bag.right, Bag.parent]; omega

/-- Sibling's x-coordinate when b is a right child (odd x). -/
theorem Bag.sibling_x_odd (b : Bag k) (hl : 1 ≤ b.l) (hodd : b.x % 2 ≠ 0) :
    (b.sibling hl).x = b.x - 1 := by
  simp only [Bag.sibling, if_neg hodd, Bag.left, Bag.parent]; omega

/-- Sibling's native interval is disjoint from b's interval. -/
theorem Bag.sibling_interval_disjoint (b : Bag k) (hl : 1 ≤ b.l) :
    Disjoint (Set.Ico b.lo b.hi) (Set.Ico (b.sibling hl).lo (b.sibling hl).hi) := by
  rw [Set.disjoint_left]
  intro r hr_b hr_sib
  rw [Set.mem_Ico] at hr_b hr_sib
  simp only [Bag.lo, Bag.hi, Bag.size, bagSize] at hr_b hr_sib
  rw [b.sibling_level_eq hl] at hr_sib
  by_cases heven : b.x % 2 = 0
  · rw [b.sibling_x_even hl heven] at hr_sib; omega
  · rw [b.sibling_x_odd hl heven, show b.x - 1 + 1 = b.x from by omega] at hr_sib; omega

/-! **1-Stranger Characterization** -/

/-- An item native to parent is a 1-stranger in b iff it's native to b's sibling.

    This is the key characterization for the j=1 case: among items in parent D's
    register set that are native to D, the 1-strangers in child B are exactly
    those native to sibling C.

    Note: General 1-strangers also include 2+-strangers (items not native to D).
    This lemma only characterizes the "newly strange" items from Seiferas Section 5. -/
theorem Bag.parent_native_one_strange_iff_sibling_native (b : Bag k) (hl : 1 ≤ b.l)
    (r : Fin (2 ^ k)) (perm : Fin (2 ^ k) → Fin (2 ^ k))
    (hparent : b.parent.Native r perm) :
    b.Strange 1 r perm ↔ (b.sibling hl).Native r perm := by
  simp only [Bag.Strange, show (1 : ℕ) ≠ 0 by omega, false_or, show 1 - 1 = 0 by omega,
    Bag.ancestor, Nat.sub_zero, pow_zero, Nat.div_one]
  simp only [Bag.Native] at hparent ⊢
  rw [b.sibling_level_eq hl]
  simp only [Bag.parent] at hparent
  -- hparent : nativeBagIdx k (b.l - 1) (perm r).val = b.x / 2
  set idx := nativeBagIdx k b.l (perm r).val
  have hparent' : idx / 2 = b.x / 2 := by
    have h1 : (b.l - 1) + 1 ≤ k := by have := b.hl; omega
    have h2 := @nativeBagIdx_div_two k (b.l - 1) (perm r).val h1
    have h3 : b.l - 1 + 1 = b.l := by omega
    rw [h3] at h2; exact h2.trans hparent
  have hidx_range : idx = 2 * (b.x / 2) ∨ idx = 2 * (b.x / 2) + 1 := by
    have h1 : idx = 2 * (idx / 2) ∨ idx = 2 * (idx / 2) + 1 := by omega
    rwa [hparent'] at h1
  by_cases heven : b.x % 2 = 0
  · -- b is left child (even x), sibling is right
    rw [b.sibling_x_even hl heven]
    have hbx : b.x = 2 * (b.x / 2) := by omega
    constructor
    · intro hne
      rcases hidx_range with h | h
      · exfalso; rw [← hbx] at h; exact hne h
      · omega
    · intro hsib; rw [hbx]; omega
  · -- b is right child (odd x), sibling is left
    rw [b.sibling_x_odd hl heven]
    have hbx : b.x = 2 * (b.x / 2) + 1 := by omega
    constructor
    · intro hne
      rcases hidx_range with h | h
      · omega
      · exfalso; rw [← hbx] at h; exact hne h
    · intro hsib; rw [hbx]; omega

/-- Sibling-native items are 1-strangers (unconditionally). -/
theorem Bag.sibling_native_is_one_strange (b : Bag k) (hl : 1 ≤ b.l)
    (r : Fin (2 ^ k)) (perm : Fin (2 ^ k) → Fin (2 ^ k))
    (hsibling : (b.sibling hl).Native r perm) :
    b.Strange 1 r perm := by
  simp only [Bag.Strange, show (1 : ℕ) ≠ 0 by omega, false_or, show 1 - 1 = 0 by omega,
    Bag.ancestor, Nat.sub_zero, pow_zero, Nat.div_one]
  simp only [Bag.Native] at hsibling ⊢
  rw [b.sibling_level_eq hl] at hsibling
  by_cases heven : b.x % 2 = 0
  · rw [b.sibling_x_even hl heven] at hsibling
    intro hb; rw [hb] at hsibling; omega
  · rw [b.sibling_x_odd hl heven] at hsibling
    intro hb; rw [hb] at hsibling; omega

/-- 1-strangers in b decompose into: higher-level strangers OR sibling-native.

    For an item to be a 1-stranger in b, either:
    1. It's also a 1-stranger in b's parent (i.e., a 2+-stranger in b), OR
    2. It's native to parent but native to sibling C (not to b)

    This is the key decomposition for the j=1 case in Seiferas (2009) Section 5. -/
theorem Bag.one_strange_decomp (b : Bag k) (hl : 1 ≤ b.l)
    (r : Fin (2 ^ k)) (perm : Fin (2 ^ k) → Fin (2 ^ k)) :
    b.Strange 1 r perm ↔
    b.parent.Strange 1 r perm ∨ (b.parent.Native r perm ∧ (b.sibling hl).Native r perm) := by
  simp only [Bag.Strange, Bag.Native, show (1 : ℕ) ≠ 0 by omega, false_or,
    show 1 - 1 = 0 by omega, Bag.ancestor, Nat.sub_zero, pow_zero, Nat.div_one]
  rw [b.sibling_level_eq hl]
  simp only [Bag.parent]
  set idx := nativeBagIdx k b.l (perm r).val
  set parent_idx := nativeBagIdx k (b.l - 1) (perm r).val
  have hparent_idx : parent_idx = idx / 2 := by
    have h1 : (b.l - 1) + 1 ≤ k := by have := b.hl; omega
    have h2 := @nativeBagIdx_div_two k (b.l - 1) (perm r).val h1
    have h3 : b.l - 1 + 1 = b.l := by omega
    rw [h3] at h2; exact h2.symm
  constructor
  · intro hne_b
    by_cases hne_parent : parent_idx ≠ b.x / 2
    · left; exact hne_parent
    · right
      push_neg at hne_parent
      constructor
      · exact hne_parent
      · have hidx_range : idx = 2 * (b.x / 2) ∨ idx = 2 * (b.x / 2) + 1 := by
          have h1 : idx = 2 * (idx / 2) ∨ idx = 2 * (idx / 2) + 1 := by omega
          have h_div : idx / 2 = b.x / 2 := by rw [← hparent_idx]; exact hne_parent
          rwa [h_div] at h1
        by_cases heven : b.x % 2 = 0
        · rw [b.sibling_x_even hl heven]
          have hbx : b.x = 2 * (b.x / 2) := by omega
          rcases hidx_range with h | h
          · exfalso; rw [← hbx] at h; exact hne_b h
          · omega
        · rw [b.sibling_x_odd hl heven]
          have hbx : b.x = 2 * (b.x / 2) + 1 := by omega
          rcases hidx_range with h | h
          · omega
          · exfalso; rw [← hbx] at h; exact hne_b h
  · intro h
    rcases h with hparent_strange | ⟨hparent_native, hsibling_native⟩
    · rw [hparent_idx] at hparent_strange
      intro heq; apply hparent_strange; rw [heq]
    · by_cases heven : b.x % 2 = 0
      · rw [b.sibling_x_even hl heven] at hsibling_native
        have hbx : b.x = 2 * (b.x / 2) := by omega
        rw [hbx]; omega
      · rw [b.sibling_x_odd hl heven] at hsibling_native
        have hbx : b.x = 2 * (b.x / 2) + 1 := by omega
        rw [hbx]; omega

/-- Parent-native ↔ native to one of the two children.

    Items in parent D's interval are in exactly one of B's or C's interval,
    since the children partition the parent. -/
theorem Bag.parent_native_iff (b : Bag k) (hl : 1 ≤ b.l)
    (r : Fin (2 ^ k)) (perm : Fin (2 ^ k) → Fin (2 ^ k)) :
    b.parent.Native r perm ↔ b.Native r perm ∨ (b.sibling hl).Native r perm := by
  constructor
  · intro hp
    by_cases hb : b.Native r perm
    · exact .inl hb
    · right
      have hstrange : b.Strange 1 r perm := by
        simp only [Bag.Strange, show (1 : ℕ) ≠ 0 by omega, false_or, show 1 - 1 = 0 by omega,
          Bag.ancestor, Nat.sub_zero, pow_zero, Nat.div_one]
        exact hb
      exact (Bag.parent_native_one_strange_iff_sibling_native b hl r perm hp).mp hstrange
  · intro h
    rcases h with hb | hs
    · exact hb.parent hl
    · rw [← b.sibling_parent_eq hl]
      exact hs.parent (by rw [b.sibling_level_eq hl]; exact hl)

end


