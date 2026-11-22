-- Prove2me | Definitions.Def_GirvingAKS_Bitonic_LayerExec
-- name    : GirvingAKS_Bitonic_LayerExec
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:31:34.438907+00:00
-- url     : https://prove2.me/theorems/08b5c4ea-f2d9-4b47-8ab5-0c8f6192fab7
-- title:
--   AKS sorting networks (Seiferas port) — Bitonic Sort — Layer Execution Helpers
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Bitonic/LayerExec.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** Bool helpers, comparator helpers, parallel layer execution, bitonic layer execution (compare + cross), decomposition lemmas, shiftEmbed helpers.
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Bitonic/LayerExec.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Bitonic_Defs
import Definitions.Def_GirvingAKS_Bitonic_Depth
import Definitions.Def_GirvingAKS_Sort_Monotone
import Definitions.Def_GirvingAKS_Sort_ZeroOne
import Definitions.Def_GirvingAKS_Sort_Depth

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Bitonic/LayerExec.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Bitonic Sort — Layer Execution Helpers

  Bool helpers, comparator helpers, parallel layer execution, bitonic layer execution
  (compare + cross), decomposition lemmas, shiftEmbed helpers.
-/


section

open Finset

/-! **Bool min/max** -/

theorem bool_min_and (a b : Bool) : min a b = (a && b) := by cases a <;> cases b <;> rfl
theorem bool_max_or (a b : Bool) : max a b = (a || b) := by cases a <;> cases b <;> rfl

/-! **Comparator Application Helpers** -/

/-- A comparator at position `c.i` produces `min`. -/
theorem apply_at_i {n : Nat} {α : Type*} [LinearOrder α]
    (c : Comparator n) (v : Fin n → α) :
    c.apply v c.i = min (v c.i) (v c.j) := by
  unfold Comparator.apply; rw [if_pos rfl]

/-- A comparator at position `c.j` produces `max`. -/
theorem apply_at_j {n : Nat} {α : Type*} [LinearOrder α]
    (c : Comparator n) (v : Fin n → α) :
    c.apply v c.j = max (v c.i) (v c.j) := by
  unfold Comparator.apply; rw [if_neg (Fin.ne_of_gt c.h), if_pos rfl]

/-- A comparator preserves values at positions other than `c.i` and `c.j`. -/
theorem apply_other {n : Nat} {α : Type*} [LinearOrder α]
    (c : Comparator n) (v : Fin n → α) (k : Fin n)
    (hki : k ≠ c.i) (hkj : k ≠ c.j) :
    c.apply v k = v k := by
  unfold Comparator.apply; rw [if_neg hki, if_neg hkj]

/-! **Parallel Layer Execution** -/

/-- In a parallel layer, executing at `c.i` gives `v(c.i) && v(c.j)`. -/
theorem parallel_layer_exec_at_i {n : Nat} (cs : List (Comparator n))
    (hpar : IsParallelLayer cs) (c : Comparator n) (hc : c ∈ cs) (v : Fin n → Bool) :
    cs.foldl (fun acc c ↦ c.apply acc) v c.i = (v c.i && v c.j) := by
  induction cs generalizing v with
  | nil => exact absurd hc List.not_mem_nil
  | cons c₀ cs ih =>
    simp only [List.foldl_cons]
    cases List.mem_cons.mp hc with
    | inl heq =>
      subst heq
      have h_untouched : ∀ c' ∈ cs, c.i ≠ c'.i ∧ c.i ≠ c'.j := by
        intro c' hc'
        have hno := (List.pairwise_cons.mp hpar).1 c' hc'
        unfold Comparator.overlaps at hno; push_neg at hno
        exact ⟨hno.1, hno.2.1⟩
      rw [foldl_comparators_outside cs (c.apply v) c.i h_untouched]
      rw [apply_at_i, bool_min_and]
    | inr hmem =>
      have hno := (List.pairwise_cons.mp hpar).1 c hmem
      unfold Comparator.overlaps at hno; push_neg at hno
      have h_vi : c₀.apply v c.i = v c.i :=
        apply_other c₀ v c.i hno.1.symm hno.2.2.1.symm
      have h_vj : c₀.apply v c.j = v c.j :=
        apply_other c₀ v c.j hno.2.1.symm hno.2.2.2.symm
      rw [ih (List.pairwise_cons.mp hpar).2 hmem, h_vi, h_vj]

/-- In a parallel layer, executing at `c.j` gives `v(c.i) || v(c.j)`. -/
theorem parallel_layer_exec_at_j {n : Nat} (cs : List (Comparator n))
    (hpar : IsParallelLayer cs) (c : Comparator n) (hc : c ∈ cs) (v : Fin n → Bool) :
    cs.foldl (fun acc c ↦ c.apply acc) v c.j = (v c.i || v c.j) := by
  induction cs generalizing v with
  | nil => exact absurd hc List.not_mem_nil
  | cons c₀ cs ih =>
    simp only [List.foldl_cons]
    cases List.mem_cons.mp hc with
    | inl heq =>
      subst heq
      have h_untouched : ∀ c' ∈ cs, c.j ≠ c'.i ∧ c.j ≠ c'.j := by
        intro c' hc'
        have hno := (List.pairwise_cons.mp hpar).1 c' hc'
        unfold Comparator.overlaps at hno; push_neg at hno
        exact ⟨hno.2.2.1, hno.2.2.2⟩
      rw [foldl_comparators_outside cs (c.apply v) c.j h_untouched]
      rw [apply_at_j, bool_max_or]
    | inr hmem =>
      have hno := (List.pairwise_cons.mp hpar).1 c hmem
      unfold Comparator.overlaps at hno; push_neg at hno
      have h_vi : c₀.apply v c.i = v c.i :=
        apply_other c₀ v c.i hno.1.symm hno.2.2.1.symm
      have h_vj : c₀.apply v c.j = v c.j :=
        apply_other c₀ v c.j hno.2.1.symm hno.2.2.2.symm
      rw [ih (List.pairwise_cons.mp hpar).2 hmem, h_vi, h_vj]

/-! **Bitonic Compare Layer Execution** -/

/-- The compare layer sends position `i < 2^k` to `v(i) && v(i + 2^k)`. -/
theorem bitonicCompareLayer_exec_left (k : Nat) (v : Fin (2^(k+1)) → Bool) (i : Fin (2^k)) :
    (bitonicCompareLayer k).exec v ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ =
    (v ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ &&
     v ⟨i.val + 2^k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩) := by
  unfold ComparatorNetwork.exec
  have hpar := bitonicCompareLayer_isParallel k
  set ci : Comparator (2^(k+1)) :=
    { i := ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩
      j := ⟨i.val + 2^k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩
      h := by simp only [Fin.lt_def]; omega }
  have hci_mem : ci ∈ (bitonicCompareLayer k).comparators := by
    simp only [bitonicCompareLayer]
    exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
  exact parallel_layer_exec_at_i _ hpar ci hci_mem v

/-- The compare layer sends position `i + 2^k` to `v(i) || v(i + 2^k)`. -/
theorem bitonicCompareLayer_exec_right (k : Nat) (v : Fin (2^(k+1)) → Bool) (i : Fin (2^k)) :
    (bitonicCompareLayer k).exec v ⟨i.val + 2^k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ =
    (v ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ ||
     v ⟨i.val + 2^k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩) := by
  unfold ComparatorNetwork.exec
  have hpar := bitonicCompareLayer_isParallel k
  set ci : Comparator (2^(k+1)) :=
    { i := ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩
      j := ⟨i.val + 2^k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩
      h := by simp only [Fin.lt_def]; omega }
  have hci_mem : ci ∈ (bitonicCompareLayer k).comparators := by
    simp only [bitonicCompareLayer]
    exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
  exact parallel_layer_exec_at_j _ hpar ci hci_mem v

/-! **Bitonic Cross Layer Execution** -/

/-- The cross layer sends position `i < 2^k` to `v(i) && v(2^(k+1) - 1 - i)`. -/
theorem bitonicCrossLayer_exec_left (k : Nat) (v : Fin (2^(k+1)) → Bool) (i : Fin (2^k)) :
    (bitonicCrossLayer k).exec v ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ =
    (v ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ &&
     v ⟨2^(k+1) - 1 - i.val, by rw [Nat.pow_succ]; omega⟩) := by
  unfold ComparatorNetwork.exec
  have hpar := bitonicCrossLayer_isParallel k
  set ci : Comparator (2^(k+1)) :=
    { i := ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩
      j := ⟨2^(k+1) - 1 - i.val, by rw [Nat.pow_succ]; omega⟩
      h := by simp only [Fin.lt_def]; have := i.isLt; rw [Nat.pow_succ]; omega }
  have hci_mem : ci ∈ (bitonicCrossLayer k).comparators := by
    simp only [bitonicCrossLayer]
    exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
  exact parallel_layer_exec_at_i _ hpar ci hci_mem v

/-- The cross layer sends position `2^(k+1) - 1 - i` to `v(i) || v(2^(k+1) - 1 - i)`. -/
theorem bitonicCrossLayer_exec_right (k : Nat) (v : Fin (2^(k+1)) → Bool) (i : Fin (2^k)) :
    (bitonicCrossLayer k).exec v ⟨2^(k+1) - 1 - i.val, by rw [Nat.pow_succ]; omega⟩ =
    (v ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ ||
     v ⟨2^(k+1) - 1 - i.val, by rw [Nat.pow_succ]; omega⟩) := by
  unfold ComparatorNetwork.exec
  have hpar := bitonicCrossLayer_isParallel k
  set ci : Comparator (2^(k+1)) :=
    { i := ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩
      j := ⟨2^(k+1) - 1 - i.val, by rw [Nat.pow_succ]; omega⟩
      h := by simp only [Fin.lt_def]; have := i.isLt; rw [Nat.pow_succ]; omega }
  have hci_mem : ci ∈ (bitonicCrossLayer k).comparators := by
    simp only [bitonicCrossLayer]
    exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
  exact parallel_layer_exec_at_j _ hpar ci hci_mem v

/-! **Execution Decomposition Lemmas** -/

/-- `bitonicMerge (k+1)` decomposes as: compare layer, then left merge, then right merge. -/
theorem bitonicMerge_exec_eq (k : Nat) {α : Type*} [LinearOrder α] (v : Fin (2^(k+1)) → α) :
    (bitonicMerge (k + 1)).exec v =
    ((bitonicMerge k).shiftEmbed (2^(k+1)) (2^k) (by rw [Nat.pow_succ]; omega)).exec
      (((bitonicMerge k).shiftEmbed (2^(k+1)) 0 (by rw [Nat.pow_succ]; omega)).exec
        ((bitonicCompareLayer k).exec v)) := by
  simp only [bitonicMerge, ComparatorNetwork.exec, List.foldl_append]

/-- `bitonicSort (k+1)` decomposes as: sort left, sort right, cross, merge left, merge right. -/
theorem bitonicSort_exec_eq (k : Nat) {α : Type*} [LinearOrder α] (v : Fin (2^(k+1)) → α) :
    (bitonicSort (k + 1)).exec v =
    ((bitonicMerge k).shiftEmbed (2^(k+1)) (2^k) (by rw [Nat.pow_succ]; omega)).exec
      (((bitonicMerge k).shiftEmbed (2^(k+1)) 0 (by rw [Nat.pow_succ]; omega)).exec
        ((bitonicCrossLayer k).exec
          (((bitonicSort k).shiftEmbed (2^(k+1)) (2^k) (by rw [Nat.pow_succ]; omega)).exec
            (((bitonicSort k).shiftEmbed (2^(k+1)) 0 (by rw [Nat.pow_succ]; omega)).exec v)))) := by
  simp only [bitonicSort, ComparatorNetwork.exec, List.foldl_append]

/-! **ShiftEmbed Execution Helpers** -/

/-- `shiftEmbed` at offset 0 acts as the original network on the local view. -/
theorem shiftEmbed_zero_exec {m : Nat} {α : Type*} [LinearOrder α]
    (net : ComparatorNetwork m) (n : Nat) (h : 0 + m ≤ n)
    (v : Fin n → α) (i : Fin m) :
    (net.shiftEmbed n 0 h).exec v ⟨i.val, by omega⟩ =
    net.exec (fun j : Fin m ↦ v ⟨j.val, by omega⟩) i := by
  have := ComparatorNetwork.shiftEmbed_exec_inside net n 0 h v i
  convert this using 2 <;> (ext; simp)

/-- `shiftEmbed` at offset `offset` acts on `⟨i.val + offset, _⟩` as the original network. -/
theorem shiftEmbed_offset_exec {m : Nat} {α : Type*} [LinearOrder α]
    (net : ComparatorNetwork m) (n offset : Nat) (h : offset + m ≤ n)
    (v : Fin n → α) (i : Fin m) :
    (net.shiftEmbed n offset h).exec v ⟨i.val + offset, by omega⟩ =
    net.exec (fun j : Fin m ↦ v ⟨j.val + offset, by omega⟩) i := by
  have := ComparatorNetwork.shiftEmbed_exec_inside net n offset h v i
  convert this using 2 <;> (ext; simp [Nat.add_comm])

end


