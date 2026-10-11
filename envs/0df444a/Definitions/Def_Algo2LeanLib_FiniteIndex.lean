-- Prove2me | Definitions.Def_Algo2LeanLib_FiniteIndex
-- name    : Algo2LeanLib_FiniteIndex
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-10T23:39:20.039683+00:00
-- url     : https://prove2.me/theorems/b6fd67fc-a24a-459c-8bae-13562065fc08
-- title:
--   Finite identifier prefixes for integer-indexed sequences
-- statement:
--   This bundle provides the finite integer range used to specify the active prefix of a total sequence. The sorter returns a permutation of these identifiers; its output remains a total sequence indexed by every integer. Finite range and indexing facts connect list-based permutation/order statements with heap sequence reads.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/Algo2LeanLib/FiniteIndex.lean

import Definitions.Def_Algo2Lean

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Finite integer ranges and injective-prefix bounds, independent of algorithms. -/
namespace Algo2Lean.FiniteIndex

/-- Integer indices from zero to `size - 1`; nonpositive sizes give an empty list. -/
def range (size : Int) : List Int := (List.range size.toNat).map Int.ofNat

@[simp] theorem range_length (size : Int) : (range size).length = size.toNat := by
  simp [range]

theorem range_nodup (size : Int) : (range size).Nodup := by
  exact List.Pairwise.map Int.ofNat (fun a b different same => different (Int.ofNat.inj same)) List.nodup_range

@[simp] theorem range_member (size vertex : Int) :
    vertex ∈ range size ↔ 0 ≤ vertex ∧ vertex < size := by
  simp only [range, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨index, bound, rfl⟩
    change 0 ≤ (index : Int) ∧ (index : Int) < size
    omega
  · rintro ⟨nonnegative, bound⟩
    exact ⟨vertex.toNat, by omega, Int.toNat_of_nonneg nonnegative⟩

/-- Erasing one present integer shortens the list by exactly one occurrence. -/
theorem erase_length (remaining : List Int) (selected : Int) (member : selected ∈ remaining) :
    (remaining.erase selected).length + 1 = remaining.length := by
  have positive := List.length_pos_of_mem member
  rw [List.length_erase_of_mem member]
  omega

/-- A duplicate-free list cannot inject by membership into a shorter list. -/
theorem nodup_subset_length (first second : List Int) (unique : first.Nodup)
    (contained : ∀ vertex ∈ first, vertex ∈ second) : first.length ≤ second.length := by
  induction first generalizing second with
  | nil => simp
  | cons vertex rest ih =>
    obtain ⟨fresh, restUnique⟩ := List.nodup_cons.mp unique
    have member := contained vertex (by simp)
    have remaining := ih (second.erase vertex) restUnique (by
      intro other inRest
      apply (List.mem_erase_of_ne (by intro same; subst other; exact fresh inRest)).mpr
      exact contained other (by simp [inRest]))
    have length := erase_length second vertex member
    simp only [List.length_cons]
    omega

/-- A finite injective prefix has no more entries than a list containing all
    its values. The `positions` left inverse establishes injectivity. -/
theorem active_prefix_bound (vertices positions : Int → Int) (size : Int)
    (nonnegative : 0 ≤ size)
    (inverse : ∀ index, 0 ≤ index → index < size → positions (vertices index) = index)
    (remaining : List Int)
    (contained : ∀ index, 0 ≤ index → index < size → vertices index ∈ remaining) :
    size ≤ (remaining.length : Int) := by
  let active := (List.range size.toNat).map (fun index : Nat => vertices (index : Int))
  have unique : active.Nodup := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem (l := List.range size.toNat) _ List.nodup_range
    intro i j iMember jMember different same
    have iBound := List.mem_range.mp iMember
    have jBound := List.mem_range.mp jMember
    have left := inverse (i : Int) (by omega) (by omega)
    have right := inverse (j : Int) (by omega) (by omega)
    rw [same] at left
    exact different (by omega)
  have included : ∀ vertex ∈ active, vertex ∈ remaining := by
    intro vertex member
    obtain ⟨index, bound, rfl⟩ := List.mem_map.mp member
    have indexBound := List.mem_range.mp bound
    exact contained (index : Int) (by omega) (by omega)
  have bound := nodup_subset_length active remaining unique included
  simp only [active, List.length_map, List.length_range] at bound
  omega

end Algo2Lean.FiniteIndex


