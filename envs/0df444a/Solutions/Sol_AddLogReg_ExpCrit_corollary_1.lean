-- Prove2me | solution 1 for AddLogReg.ExpCrit.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:44:33.475017+00:00
-- url     : https://prove2.me/submissions/c3188957-a1d8-43a7-aae4-3aef0cde7ea7

import Mathlib
import Definitions.Def_AddLogReg_ExpCrit_Setting

set_option autoImplicit false
open MeasureTheory ProbabilityTheory AddLogReg.ExpCrit

theorem solution (n : ℕ) (y : Fin n → Bool) (hpos : ∃ i, y i = true)
    (hneg : ∃ i, y i = false) :
    let npos : ℕ := (Finset.univ.filter (fun i => y i = true)).card
    let nneg : ℕ := (Finset.univ.filter (fun i => y i = false)).card
    let c : ℝ := (1 / 2) * Real.log ((npos : ℝ) / nneg)
    (∀ c' : ℝ, (1 / (n : ℝ)) * ∑ i, Real.exp (-(sgn (y i) * c)) ≤
        (1 / (n : ℝ)) * ∑ i, Real.exp (-(sgn (y i) * c'))) ∧
    (npos : ℝ) / n = Real.exp c / (Real.exp (-c) + Real.exp c) ∧
    (nneg : ℝ) / n = Real.exp (-c) / (Real.exp (-c) + Real.exp c) := by
  intro npos nneg c
  have hp : 0 < npos := by
    obtain ⟨i, hi⟩ := hpos
    exact Finset.card_pos.2 ⟨i, by simp [hi]⟩
  have hq : 0 < nneg := by
    obtain ⟨i, hi⟩ := hneg
    exact Finset.card_pos.2 ⟨i, by simp [hi]⟩
  have hn : (n : ℝ) = npos + nneg := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun i => y i = true)
    simp only [Finset.card_univ, Fintype.card_fin, Bool.not_eq_true] at h
    have : n = npos + nneg := h.symm
    exact_mod_cast this
  have hpR : (0 : ℝ) < npos := by exact_mod_cast hp
  have hqR : (0 : ℝ) < nneg := by exact_mod_cast hq
  have hsum : ∀ c' : ℝ, ∑ i, Real.exp (-(sgn (y i) * c')) =
      npos * Real.exp (-c') + nneg * Real.exp c' := by
    intro c'
    have : ∀ i, Real.exp (-(sgn (y i) * c')) =
        if y i = true then Real.exp (-c') else Real.exp c' := by
      intro i; cases y i <;> simp [sgn]
    simp_rw [this]
    rw [Finset.sum_ite]
    simp [npos, nneg, Finset.sum_const, nsmul_eq_mul]
  set s : ℝ := Real.exp c with hs
  have hspos : 0 < s := Real.exp_pos _
  have hs2 : s ^ 2 = npos / nneg := by
    rw [hs, sq, ← Real.exp_add, ← two_mul]
    have : 2 * c = Real.log ((npos : ℝ) / nneg) := by simp only [c]; ring
    rw [this, Real.exp_log (div_pos hpR hqR)]
  have hp_eq : (npos : ℝ) = nneg * s ^ 2 := by rw [hs2]; field_simp
  have hnegc : Real.exp (-c) = s⁻¹ := by rw [Real.exp_neg]
  refine ⟨?_, ?_, ?_⟩
  · intro c'
    rw [hsum, hsum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    set t : ℝ := Real.exp c' with ht
    have htpos : 0 < t := Real.exp_pos _
    rw [hnegc, Real.exp_neg, ← ht, hp_eq]
    rw [← sub_nonneg]
    have : nneg * s ^ 2 * t⁻¹ + nneg * t - (nneg * s ^ 2 * s⁻¹ + nneg * s) = nneg * (s - t) ^ 2 / t := by
      field_simp
      ring
    rw [this]; exact div_nonneg (mul_nonneg hqR.le (sq_nonneg _)) htpos.le
  · rw [hnegc, hn, hp_eq]
    field_simp
    ring
  · rw [hnegc, hn, hp_eq]
    field_simp
    ring
