-- Prove2me | solution 1 for ADH2015.qutrit_marginals_maximallyMixed
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T14:22:23.765703+00:00
-- url     : https://prove2.me/submissions/17ecf24a-a154-46e2-ba55-38f83e842181

import Mathlib
import Definitions.Def_ADH2015_defs

open Matrix
open scoped Kronecker
open ADH2015

lemma adh_encode_eq (f : Qutrit → ℂ) (x : (Qutrit × Qutrit) × Qutrit) :
    ADH2015.encode f x = if x.2 = x.1.2 + x.1.2 - x.1.1 then
      f (x.1.2 - x.1.1) * ((1 / Real.sqrt 3 : ℝ) : ℂ) else 0 := by
  obtain ⟨⟨p, q⟩, r⟩ := x
  simp only [ADH2015.encode, ADH2015.codeKet, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Fin.sum_univ_three]
  fin_cases p <;> fin_cases q <;> fin_cases r <;>
    simp [show (-1 : Fin 3) = 2 from rfl, show (-2 : Fin 3) = 1 from rfl]

theorem solution (a : Qutrit → ℂ) (ha : ∑ i, Complex.normSq (a i) = 1)
    (k : Fin 3) : ADH2015.reducedQutrit (ADH2015.encode a) k = (1 / 3 : ℂ) • 1 := by
  have ht : (Real.sqrt 3 : ℂ)⁻¹ * (Real.sqrt 3 : ℂ)⁻¹ = 3⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; push_cast; rfl
  have ha' : a 0 * (starRingEnd ℂ) (a 0) + a 1 * (starRingEnd ℂ) (a 1) +
      a 2 * (starRingEnd ℂ) (a 2) = 1 := by
    simp only [Complex.mul_conj]
    rw [Fin.sum_univ_three] at ha
    exact_mod_cast ha
  ext x y
  simp only [ADH2015.reducedQutrit, of_apply, adh_encode_eq, Fin.sum_univ_three]
  fin_cases k <;> fin_cases x <;> fin_cases y <;>
    simp [show (-1 : Fin 3) = 2 from rfl, show (-2 : Fin 3) = 1 from rfl]
  all_goals linear_combination ((Real.sqrt 3 : ℂ)⁻¹ * (Real.sqrt 3 : ℂ)⁻¹) * ha' + ht
