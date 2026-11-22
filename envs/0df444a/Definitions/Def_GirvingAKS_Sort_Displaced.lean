-- Prove2me | Definitions.Def_GirvingAKS_Sort_Displaced
-- name    : GirvingAKS_Sort_Displaced
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:30:27.311652+00:00
-- url     : https://prove2.me/theorems/be0bfbde-aa71-4e59-bb80-70040be5fbb9
-- title:
--   AKS sorting networks (Seiferas port) — Displaced Count Monotonicity for Comparator Networks
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Sort/Displaced.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** A comparator network can only decrease the "displaced count" — the number of small values at high positions (or large values at low positions). This is a key structural property used in the separator correctness proof.
--
--   Main results:
--
--   - `exec_displaced_le`: small values at high positions can only decrease
--   - `exec_displaced_final_le`: large values at low positions can only decrease
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Sort/Displaced.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Sort_Defs

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Sort/Displaced.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Displaced Count Monotonicity for Comparator Networks

  A comparator network can only decrease the "displaced count" — the number
  of small values at high positions (or large values at low positions).
  This is a key structural property used in the separator correctness proof.

  Main results:
  • `exec_displaced_le`: small values at high positions can only decrease
  • `exec_displaced_final_le`: large values at low positions can only decrease
-/


section


open Finset BigOperators

/-! **Comparator helpers** -/

/-- When `w(c.i) ≤ w(c.j)`, the comparator is identity. -/
lemma Comparator.apply_eq_of_le {n : ℕ} {α : Type*} [LinearOrder α]
    (c : Comparator n) (w : Fin n → α) (h : w c.i ≤ w c.j) :
    c.apply w = w := by
  ext pos; unfold Comparator.apply
  by_cases hpi : pos = c.i
  · rw [if_pos hpi, hpi, min_eq_left h]
  · rw [if_neg hpi]; by_cases hpj : pos = c.j
    · rw [if_pos hpj, hpj, max_eq_right h]
    · rw [if_neg hpj]

/-- When `w(c.j) < w(c.i)`, the comparator swaps positions `i` and `j`. -/
lemma Comparator.apply_eq_swap {n : ℕ} {α : Type*} [LinearOrder α]
    (c : Comparator n) (w : Fin n → α) (h : w c.j < w c.i) (pos : Fin n) :
    c.apply w pos = w (Equiv.swap c.i c.j pos) := by
  unfold Comparator.apply
  by_cases hpi : pos = c.i
  · rw [if_pos hpi, hpi, min_eq_right h.le, Equiv.swap_apply_left]
  · rw [if_neg hpi]; by_cases hpj : pos = c.j
    · rw [if_pos hpj, hpj, max_eq_left h.le, Equiv.swap_apply_right]
    · rw [if_neg hpj, Equiv.swap_apply_of_ne_of_ne hpi hpj]


/-! **SepInitial direction: small values at high positions** -/

/-- A single comparator does not increase the count of small values at high positions.
    At position `c.j` (higher), the comparator places `max`, which is harder
    to be `< threshold`. -/
lemma apply_displaced_le {n : ℕ} (c : Comparator n) (w : Fin n → Fin n)
    (B threshold : ℕ) :
    (univ.filter (fun pos : Fin n ↦
      B ≤ pos.val ∧ (c.apply w pos).val < threshold)).card ≤
    (univ.filter (fun pos : Fin n ↦
      B ≤ pos.val ∧ (w pos).val < threshold)).card := by
  by_cases hle : w c.i ≤ w c.j
  · rw [c.apply_eq_of_le w hle]
  · push_neg at hle
    by_cases hBi : B ≤ c.i.val
    · -- B ≤ c.i: swap bijection preserves cardinality
      have hBj : B ≤ c.j.val := le_trans hBi (le_of_lt c.h)
      apply le_of_eq
      apply Finset.card_nbij' (Equiv.swap c.i c.j) (Equiv.swap c.i c.j)
      · intro pos hp
        simp only [SetLike.mem_coe, Finset.mem_coe, mem_filter, mem_univ, true_and] at hp ⊢
        refine ⟨?_, by rw [c.apply_eq_swap w hle] at hp
                       simpa [Equiv.swap_apply_self] using hp.2⟩
        by_cases hpi : pos = c.i
        · rw [hpi, Equiv.swap_apply_left]; exact hBj
        · by_cases hpj : pos = c.j
          · rw [hpj, Equiv.swap_apply_right]; exact hBi
          · rw [Equiv.swap_apply_of_ne_of_ne hpi hpj]; exact hp.1
      · intro pos hp
        simp only [SetLike.mem_coe, Finset.mem_coe, mem_filter, mem_univ, true_and] at hp ⊢
        refine ⟨?_, by rw [c.apply_eq_swap w hle]
                       simpa [Equiv.swap_apply_self] using hp.2⟩
        by_cases hpi : pos = c.i
        · rw [hpi, Equiv.swap_apply_left]; exact hBj
        · by_cases hpj : pos = c.j
          · rw [hpj, Equiv.swap_apply_right]; exact hBi
          · rw [Equiv.swap_apply_of_ne_of_ne hpi hpj]; exact hp.1
      · intro _ _; simp [Equiv.swap_apply_self]
      · intro _ _; simp [Equiv.swap_apply_self]
    · -- c.i < B: subset argument
      push_neg at hBi
      apply Finset.card_le_card
      intro pos hp
      simp only [mem_filter, mem_univ, true_and] at hp ⊢
      refine ⟨hp.1, ?_⟩
      rw [c.apply_eq_swap w hle] at hp
      by_cases hpi : pos = c.i
      · subst hpi; omega
      · by_cases hpj : pos = c.j
        · subst hpj; rw [Equiv.swap_apply_right] at hp; exact lt_trans hle hp.2
        · rw [Equiv.swap_apply_of_ne_of_ne hpi hpj] at hp; exact hp.2

/-- A comparator network does not increase the count of small values at high positions. -/
theorem exec_displaced_le {n : ℕ} (net : ComparatorNetwork n)
    (w : Fin n → Fin n) (B threshold : ℕ) :
    (univ.filter (fun pos : Fin n ↦
      B ≤ pos.val ∧ (net.exec w pos).val < threshold)).card ≤
    (univ.filter (fun pos : Fin n ↦
      B ≤ pos.val ∧ (w pos).val < threshold)).card := by
  unfold ComparatorNetwork.exec
  induction net.comparators generalizing w with
  | nil => exact le_refl _
  | cons c cs ih =>
    simp only [List.foldl_cons]
    exact le_trans (ih (c.apply w)) (apply_displaced_le c w B threshold)


/-! **SepFinal direction: large values at low positions** -/

/-- A single comparator does not increase large values at low positions.
    At position `c.i` (lower), the comparator places `min`, which is harder
    to be `≥ threshold`. -/
lemma apply_displaced_final_le {n : ℕ} (c : Comparator n) (w : Fin n → Fin n)
    (B threshold : ℕ) :
    (univ.filter (fun pos : Fin n ↦
      pos.val < B ∧ threshold ≤ (c.apply w pos).val)).card ≤
    (univ.filter (fun pos : Fin n ↦
      pos.val < B ∧ threshold ≤ (w pos).val)).card := by
  by_cases hle : w c.i ≤ w c.j
  · rw [c.apply_eq_of_le w hle]
  · push_neg at hle
    have hsw : ∀ q, c.apply w q = w (Equiv.swap c.i c.j q) := c.apply_eq_swap w hle
    by_cases hBj : c.j.val < B
    · -- Both below B: swap bijection preserves cardinality
      have hBi : c.i.val < B := lt_trans c.h hBj
      apply le_of_eq
      apply Finset.card_nbij' (Equiv.swap c.i c.j) (Equiv.swap c.i c.j)
      · intro pos hp
        simp only [SetLike.mem_coe, Finset.mem_coe, mem_filter, mem_univ, true_and] at hp ⊢
        refine ⟨?_, ?_⟩
        · by_cases hpi : pos = c.i
          · rw [hpi, Equiv.swap_apply_left]; exact hBj
          · by_cases hpj : pos = c.j
            · rw [hpj, Equiv.swap_apply_right]; exact hBi
            · rw [Equiv.swap_apply_of_ne_of_ne hpi hpj]; exact hp.1
        · rw [hsw pos] at hp; simpa [Equiv.swap_apply_self] using hp.2
      · intro pos hp
        simp only [SetLike.mem_coe, Finset.mem_coe, mem_filter, mem_univ, true_and] at hp ⊢
        refine ⟨?_, ?_⟩
        · by_cases hpi : pos = c.i
          · rw [hpi, Equiv.swap_apply_left]; exact hBj
          · by_cases hpj : pos = c.j
            · rw [hpj, Equiv.swap_apply_right]; exact hBi
            · rw [Equiv.swap_apply_of_ne_of_ne hpi hpj]; exact hp.1
        · rw [hsw (Equiv.swap c.i c.j pos), Equiv.swap_apply_self]; exact hp.2
      · intro _ _; simp [Equiv.swap_apply_self]
      · intro _ _; simp [Equiv.swap_apply_self]
    · -- c.j ≥ B: subset (c.i gets min ≤ w(c.i), c.j not counted)
      push_neg at hBj
      apply Finset.card_le_card
      intro pos hp
      simp only [mem_filter, mem_univ, true_and] at hp ⊢
      refine ⟨hp.1, ?_⟩
      rw [hsw pos] at hp
      by_cases hpi : pos = c.i
      · subst hpi; rw [Equiv.swap_apply_left] at hp; exact le_trans hp.2 hle.le
      · by_cases hpj : pos = c.j
        · subst hpj; omega
        · rw [Equiv.swap_apply_of_ne_of_ne hpi hpj] at hp; exact hp.2

/-- A comparator network does not increase large values at low positions. -/
theorem exec_displaced_final_le {n : ℕ} (net : ComparatorNetwork n)
    (w : Fin n → Fin n) (B threshold : ℕ) :
    (univ.filter (fun pos : Fin n ↦
      pos.val < B ∧ threshold ≤ (net.exec w pos).val)).card ≤
    (univ.filter (fun pos : Fin n ↦
      pos.val < B ∧ threshold ≤ (w pos).val)).card := by
  unfold ComparatorNetwork.exec
  induction net.comparators generalizing w with
  | nil => exact le_refl _
  | cons c cs ih =>
    simp only [List.foldl_cons]
    exact le_trans (ih (c.apply w)) (apply_displaced_final_le c w B threshold)

end


