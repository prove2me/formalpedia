-- Prove2me | solution 1 for ApproxPolySatCH.Main.gauss_strict_of_valuation_shift
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:37:40.213121+00:00
-- url     : https://prove2.me/submissions/2c1b242f-dd47-4c76-acfd-e7f76b6281e4

import Definitions.Def_ApproxPolySatCH_Main_ResultantLanguages

set_option autoImplicit false

open ApproxPolySatCH.Main

theorem solution {k : Type} [Field k] (v : EpsilonValuation k)
    (q r : Polynomial (ValuedClosure k)) (D N : ℕ) (hq : q ≠ 0)
    (hbound : ∀ i, q.coeff i ≠ 0 → v.val (q.coeff i) ≤ (D : WithTop ℚ))
    (hmatch : ∀ i, q.coeff i ≠ 0 →
      v.val (r.coeff i) = v.val (q.coeff i) + (N : WithTop ℚ))
    (htail : ∀ i, q.coeff i = 0 →
      ((N + D : ℕ) : WithTop ℚ) < v.val (r.coeff i)) :
    gaussValuation v q < v.val (q.eval 0) ↔
      gaussValuation v r < v.val (r.eval 0) := by
  have hqs : q.support.Nonempty := Polynomial.support_nonempty.mpr hq
  obtain ⟨j, hj, hmin⟩ := Finset.exists_mem_eq_inf q.support hqs
    (fun i => v.val (q.coeff i))
  have hjq : q.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
  have hgq : gaussValuation v q = v.val (q.coeff j) := hmin
  have hgD : gaussValuation v q ≤ (D : WithTop ℚ) := by
    rw [hgq]
    exact hbound j hjq
  have hrj : r.coeff j ≠ 0 := by
    have hfin : v.val (r.coeff j) ≤ ((D + N : ℕ) : WithTop ℚ) := by
      rw [hmatch j hjq]
      simpa [Nat.cast_add, add_comm] using add_le_add (hbound j hjq) (le_refl (N : WithTop ℚ))
    intro hz
    rw [hz, v.zero] at hfin
    simp at hfin
  have hgauss : gaussValuation v r = gaussValuation v q + (N : WithTop ℚ) := by
    apply le_antisymm
    · calc
        gaussValuation v r ≤ v.val (r.coeff j) :=
          Finset.inf_le (Polynomial.mem_support_iff.mpr hrj)
        _ = v.val (q.coeff j) + (N : WithTop ℚ) := hmatch j hjq
        _ = gaussValuation v q + (N : WithTop ℚ) := by rw [hgq]
    · apply Finset.le_inf
      intro i hi
      by_cases hqi : q.coeff i = 0
      · exact le_of_lt (calc
          gaussValuation v q + (N : WithTop ℚ) ≤ (D : WithTop ℚ) + (N : WithTop ℚ) :=
            add_le_add hgD (le_refl _)
          _ = ((N + D : ℕ) : WithTop ℚ) := by simp [Nat.cast_add, add_comm]
          _ < v.val (r.coeff i) := htail i hqi)
      · have hiq : i ∈ q.support := Polynomial.mem_support_iff.mpr hqi
        calc
          gaussValuation v q + (N : WithTop ℚ) ≤ v.val (q.coeff i) + (N : WithTop ℚ) :=
            add_le_add (Finset.inf_le hiq) (le_refl _)
          _ = v.val (r.coeff i) := (hmatch i hqi).symm
  by_cases hq0 : q.coeff 0 = 0
  · have hleft : gaussValuation v q < v.val (q.eval 0) := by
      rw [← Polynomial.coeff_zero_eq_eval_zero, hq0, v.zero]
      exact lt_of_le_of_lt hgD (by simp)
    have hright : gaussValuation v r < v.val (r.eval 0) := by
      rw [← Polynomial.coeff_zero_eq_eval_zero, hgauss]
      exact calc
        gaussValuation v q + (N : WithTop ℚ) ≤ (D : WithTop ℚ) + (N : WithTop ℚ) :=
          add_le_add hgD (le_refl _)
        _ = ((N + D : ℕ) : WithTop ℚ) := by simp [Nat.cast_add, add_comm]
        _ < v.val (r.coeff 0) := htail 0 hq0
    exact iff_of_true hleft hright
  · rw [← Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.coeff_zero_eq_eval_zero,
      hgauss, hmatch 0 hq0]
    exact (WithTop.add_lt_add_iff_right (WithTop.natCast_ne_top N)).symm
