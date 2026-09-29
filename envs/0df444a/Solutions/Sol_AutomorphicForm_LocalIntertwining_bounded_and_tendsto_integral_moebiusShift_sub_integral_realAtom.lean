-- Prove2me | solution 1 for AutomorphicForm.LocalIntertwining.bounded_and_tendsto_integral_moebiusShift_sub_integral_realAtom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/7579dafd-7a46-5ebb-b117-c5b126b48464

import Mathlib
import Theorems.Thm_MeasureTheory_integral_abs_det_div_sq_mul_comp_moebius_real
import Theorems.Thm_AutomorphicForm_LocalIntertwining_tendsto_integral_sq_rpow_sub_one_mul_realAtom_nhdsGT_one_half
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_LocalIntertwining_bounded_and_tendsto_integral_moebiusShift_sub_integral_realAtom

set_option autoImplicit false

open MeasureTheory Filter Topology

noncomputable section

namespace ARCHW3R

def atom (k : ℤ) (σ x : ℝ) : ℂ :=
  ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-((σ : ℂ) + 1 / 2))

theorem one_add_sq_pos (x : ℝ) : 0 < 1 + x ^ 2 := by positivity

theorem norm_phase (x : ℝ) : ‖(((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)‖ = 1 := by
  have h1 : ‖((x : ℝ) : ℂ) - Complex.I‖ = Real.sqrt (1 + x ^ 2) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]; congr 1; simp; ring
  have h2 : Real.sqrt (1 + x ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (one_add_sq_pos x)).ne'
  rw [norm_div, h1, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), div_self h2]

theorem norm_atom (k : ℤ) (σ x : ℝ) : ‖atom k σ x‖ = (1 + x ^ 2) ^ (-(σ + 1 / 2)) := by
  rw [atom, norm_mul, norm_zpow, norm_phase, one_zpow, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (one_add_sq_pos x)]
  congr 1
  simp

theorem norm_atom_le (k : ℤ) {σ : ℝ} (hσ : 1 / 2 ≤ σ) (x : ℝ) : ‖atom k σ x‖ ≤ (1 + x ^ 2)⁻¹ := by
  rw [norm_atom, ← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg x]) (by linarith)

theorem continuous_phase : Continuous fun x : ℝ => (((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ) := by
  refine Continuous.div (by fun_prop) (by fun_prop) fun x => ?_
  exact_mod_cast (Real.sqrt_pos.mpr (one_add_sq_pos x)).ne'

theorem continuous_atom (k : ℤ) (σ : ℝ) : Continuous (atom k σ) := by
  unfold atom
  refine Continuous.mul (continuous_phase.zpow₀ k fun x => Or.inl ?_) ?_
  · intro h
    have := norm_phase x
    rw [h, norm_zero] at this
    exact zero_ne_one this
  · refine Continuous.cpow (by fun_prop) continuous_const fun x => ?_
    exact_mod_cast Complex.ofReal_mem_slitPlane.mpr (one_add_sq_pos x)

theorem integrable_atom (k : ℤ) {σ : ℝ} (hσ : 1 / 2 ≤ σ) : Integrable (atom k σ) :=
  Integrable.mono' integrable_inv_one_add_sq (continuous_atom k σ).aestronglyMeasurable
    (ae_of_all _ (norm_atom_le k hσ))

theorem sq_le (c' d' x : ℝ) : (c' * x + d') ^ 2 ≤ (c' ^ 2 + d' ^ 2) * (1 + x ^ 2) := by
  nlinarith [sq_nonneg (c' - d' * x)]

theorem integrable_weighted (c' d' : ℝ) (k : ℤ) {σ : ℝ} (hσ : 1 / 2 < σ) :
    Integrable fun x : ℝ => ((((c' * x + d') ^ 2) ^ (σ - 1 / 2) : ℝ) : ℂ) * atom k σ x := by
  set t : ℝ := σ - 1 / 2 with ht
  have ht0 : 0 ≤ t := by rw [ht]; linarith
  set K : ℝ := c' ^ 2 + d' ^ 2 with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (K ^ t)) ?_ (ae_of_all _ fun x => ?_)
  · refine Continuous.aestronglyMeasurable (Continuous.mul ?_ (continuous_atom k σ))
    refine Complex.continuous_ofReal.comp ?_
    exact Continuous.rpow_const (by fun_prop) fun x => Or.inr ht0
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (sq_nonneg _) _), norm_atom]
    have h1 : ((c' * x + d') ^ 2) ^ t ≤ K ^ t * (1 + x ^ 2) ^ t := by
      rw [← Real.mul_rpow hK0 (one_add_sq_pos x).le]
      exact Real.rpow_le_rpow (sq_nonneg _) (sq_le c' d' x) ht0
    have h2 : (1 + x ^ 2) ^ t * (1 + x ^ 2) ^ (-(σ + 1 / 2)) = (1 + x ^ 2)⁻¹ := by
      rw [← Real.rpow_add (one_add_sq_pos x), ← Real.rpow_neg_one]
      congr 1; rw [ht]; ring
    calc ((c' * x + d') ^ 2) ^ t * (1 + x ^ 2) ^ (-(σ + 1 / 2))
        ≤ K ^ t * (1 + x ^ 2) ^ t * (1 + x ^ 2) ^ (-(σ + 1 / 2)) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (one_add_sq_pos x).le _)
      _ = K ^ t * (1 + x ^ 2)⁻¹ := by rw [mul_assoc, h2]

theorem jacobian_identity (a b c d : ℝ) (hdet : a * d - b * c ≠ 0) {σ : ℝ} (hσ : 1 / 2 < σ) (x : ℝ) :
    (((|a * d - b * c| / (a + x * c) ^ 2 : ℝ)) : ℂ)
        * (((((-c / Real.sqrt |a * d - b * c|) * ((b + x * d) / (a + x * c)) + d / Real.sqrt |a * d - b * c|) ^ 2)
              ^ (σ - 1 / 2) : ℝ) : ℂ)
      = (((|a * d - b * c| : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2) * ((|a + x * c| : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1))) := by
  set D : ℝ := |a * d - b * c| with hD
  have hD0 : 0 < D := abs_pos.mpr hdet
  set t : ℝ := a + x * c with ht
  by_cases ht0 : t = 0
  · have hne : (-(2 * (σ : ℂ) + 1)) ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      simp at this
      linarith
    rw [ht0]
    have h1 : ((|(0 : ℝ)| : ℝ) : ℂ) = 0 := by simp
    rw [h1, Complex.zero_cpow hne, mul_zero]
    simp
  · have hs : Real.sqrt D ≠ 0 := (Real.sqrt_pos.mpr hD0).ne'
    have hW : ((-c / Real.sqrt D) * ((b + x * d) / t) + d / Real.sqrt D) ^ 2 = D / t ^ 2 := by
      have e1 : (-c / Real.sqrt D) * ((b + x * d) / t) + d / Real.sqrt D = (a * d - b * c) / (t * Real.sqrt D) := by
        field_simp
        rw [ht]; ring
      rw [e1, div_pow, mul_pow, Real.sq_sqrt hD0.le]
      have h2 : (a * d - b * c) ^ 2 = D ^ 2 := by rw [hD, sq_abs]
      have hDne : D ≠ 0 := hD0.ne'
      rw [h2]
      field_simp
    rw [hW]
    have hq : 0 < D / t ^ 2 := div_pos hD0 (by positivity)
    rw [show ((σ : ℂ) + 1 / 2) = ((σ + 1 / 2 : ℝ) : ℂ) by push_cast; ring,
      show (-(2 * (σ : ℂ) + 1)) = ((-(2 * σ + 1) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow hD0.le, ← Complex.ofReal_cpow (abs_nonneg t), ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    calc D / t ^ 2 * (D / t ^ 2) ^ (σ - 1 / 2)
        = (D / t ^ 2) ^ (1 + (σ - 1 / 2)) := by rw [Real.rpow_add hq, Real.rpow_one]
      _ = (D / t ^ 2) ^ (σ + 1 / 2) := by congr 1; ring
      _ = D ^ (σ + 1 / 2) / (|t| ^ 2) ^ (σ + 1 / 2) := by rw [Real.div_rpow hD0.le (sq_nonneg t), sq_abs]
      _ = D ^ (σ + 1 / 2) * |t| ^ (-(2 * σ + 1)) := by
          rw [show (|t| ^ 2 : ℝ) = |t| ^ (2 : ℝ) by rw [← Real.rpow_natCast]; norm_num,
            ← Real.rpow_mul (abs_nonneg t), Real.rpow_neg (abs_nonneg t), div_eq_mul_inv]
          congr 2; ring

theorem main (a b c d : ℝ) (hdet : a * d - b * c ≠ 0) (k : ℤ) :
    (∃ C : ℝ, ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 → ‖∫ x, atom k σ x‖ ≤ C) ∧
    Tendsto (fun σ : ℝ =>
        (∫ x : ℝ, (((|a * d - b * c| : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2) * ((|a + x * c| : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)))
            * atom k σ ((b + x * d) / (a + x * c)))
          - ∫ x : ℝ, atom k σ x)
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by
  constructor
  · refine ⟨∫ x : ℝ, (1 + x ^ 2)⁻¹, fun σ hσ _ => ?_⟩
    refine (norm_integral_le_integral_norm _).trans ?_
    exact integral_mono_of_nonneg (ae_of_all _ fun x => norm_nonneg _) integrable_inv_one_add_sq
      (ae_of_all _ (norm_atom_le k hσ.le))
  · have hD0 : 0 < |a * d - b * c| := abs_pos.mpr hdet
    have hs : Real.sqrt |a * d - b * c| ≠ 0 := (Real.sqrt_pos.mpr hD0).ne'
    have hcd : (-c / Real.sqrt |a * d - b * c|) ≠ 0 ∨ (d / Real.sqrt |a * d - b * c|) ≠ 0 := by
      by_contra h
      rw [not_or, not_not, not_not, div_eq_zero_iff, neg_eq_zero, div_eq_zero_iff] at h
      apply hdet
      rw [h.1.resolve_right hs, h.2.resolve_right hs]; ring
    have hA4 := AutomorphicForm.LocalIntertwining.tendsto_integral_sq_rpow_sub_one_mul_realAtom_nhdsGT_one_half
      (-c / Real.sqrt |a * d - b * c|) (d / Real.sqrt |a * d - b * c|) hcd k
    refine hA4.congr' (eventually_nhdsWithin_of_forall fun σ hσ => ?_)
    have hσ' : 1 / 2 < σ := hσ
    change ∫ x : ℝ, (((((-c / Real.sqrt |a * d - b * c|) * x + d / Real.sqrt |a * d - b * c|) ^ 2) ^ (σ - 1 / 2) - 1 : ℝ) : ℂ)
        * atom k σ x = _
    have hsplit : (fun x : ℝ => (((((-c / Real.sqrt |a * d - b * c|) * x + d / Real.sqrt |a * d - b * c|) ^ 2)
          ^ (σ - 1 / 2) - 1 : ℝ) : ℂ) * atom k σ x)
        = fun x : ℝ => (((((-c / Real.sqrt |a * d - b * c|) * x + d / Real.sqrt |a * d - b * c|) ^ 2)
          ^ (σ - 1 / 2) : ℝ) : ℂ) * atom k σ x - atom k σ x := by
      funext x; push_cast; ring
    rw [hsplit, integral_sub (integrable_weighted _ _ k hσ') (integrable_atom k hσ'.le)]
    congr 1
    rw [← MeasureTheory.integral_abs_det_div_sq_mul_comp_moebius_real a b c d hdet
      (fun u => (((((-c / Real.sqrt |a * d - b * c|) * u + d / Real.sqrt |a * d - b * c|) ^ 2) ^ (σ - 1 / 2) : ℝ) : ℂ)
        * atom k σ u)]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only
    rw [← mul_assoc, jacobian_identity a b c d hdet hσ' x]

end ARCHW3R

end

theorem solution
    (a b c d : ℝ) (_hdet : a * d - b * c ≠ 0) (k : ℤ) :
    let atom : ℝ → ℝ → ℂ := fun σ x =>
      ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-((σ : ℂ) + 1 / 2))
    (∃ C : ℝ, ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 → ‖∫ x, atom σ x‖ ≤ C) ∧
    Tendsto (fun σ : ℝ =>
        (∫ x : ℝ, (((|a * d - b * c| : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2) * ((|a + x * c| : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)))
            * atom σ ((b + x * d) / (a + x * c)))
          - ∫ x : ℝ, atom σ x)
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by
  exact ARCHW3R.main a b c d _hdet k

end S_AutomorphicForm_LocalIntertwining_bounded_and_tendsto_integral_moebiusShift_sub_integral_realAtom
end P2MW
export P2MW.S_AutomorphicForm_LocalIntertwining_bounded_and_tendsto_integral_moebiusShift_sub_integral_realAtom (solution)
