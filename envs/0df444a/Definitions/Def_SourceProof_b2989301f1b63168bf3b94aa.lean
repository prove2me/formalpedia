-- Prove2me | Definitions.Def_SourceProof_b2989301f1b63168bf3b94aa
-- name    : SourceProof_b2989301f1b63168bf3b94aa
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:47:16.356382+00:00
-- url     : https://prove2.me/theorems/06a1ad54-d880-4f7b-9518-1c05f35cc257
-- title:
--   LevyStochCalc source module: SourceProof_b2989301f1b63168bf3b94aa
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.lintegral_lintegral_sq_le_bieleckiNorm_sq` comes from the `LevyStochCalc.Ito.PicardOutputWeighting` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardOutputWeighting_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Bielecki weighting and the per-component difference bounds

The Bielecki norm with rate `β` dominates the second moment at each time of `[0, T]` after
reweighting by `e^{2βs}`, and the doubly-integrated energy over `[0, t]` by
`e^{2βt}/(2β)`, the factor `1/(2β)` being what makes the Picard rate small for large `β`.
Combined with the Lipschitz bounds on the coefficients this bounds the drift, diffusion and
jump components of the difference of two Picard steps by the energy of the difference of the
two frozen paths.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
variable {n d : ℕ} {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]

section Weighting

omit [MeasurableSpace E] in

theorem _root_.Prove2MeSourceProof.h_b2989301f1b63168bf3b94aa {β : ℝ} (hβ : 0 < β) (T : ℝ)
    (Z : ℝ → Ω → (Fin n → ℝ))
    (hZ : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => Z s ω))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2) ∂volume ∂P
      ≤ ENNReal.ofReal (Real.exp (2 * β * t) / (2 * β))
          * (bieleckiNorm (P := P) β T Z) ^ (2 : ℕ) := by
  have hβ2 : (0 : ℝ) < 2 * β := by linarith
  -- the exponential window integral
  have hexp : ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (Real.exp (2 * β * s)) ∂volume
      ≤ ENNReal.ofReal (Real.exp (2 * β * t) / (2 * β)) := by
    have hcont : Continuous fun s : ℝ => Real.exp (2 * β * s) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    have hint : MeasureTheory.IntegrableOn (fun s : ℝ => Real.exp (2 * β * s))
        (Set.Icc (0 : ℝ) t) volume :=
      (hcont.continuousOn).integrableOn_compact isCompact_Icc
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun s => Real.exp_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hIcc : (∫ s in Set.Icc (0 : ℝ) t, Real.exp (2 * β * s) ∂volume)
        = ∫ s in (0 : ℝ)..t, Real.exp (2 * β * s) := by
      rw [intervalIntegral.integral_of_le ht.1,
        MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioc_ae_eq_Icc]
    rw [hIcc, intervalIntegral.integral_comp_mul_left Real.exp (ne_of_gt hβ2),
      integral_exp, mul_zero, Real.exp_zero, smul_eq_mul]
    rw [div_eq_inv_mul]
    have hexp_pos : (0 : ℝ) < Real.exp (2 * β * t) := Real.exp_pos _
    have hinv : (0 : ℝ) < (2 * β)⁻¹ := by positivity
    nlinarith [hinv, hexp_pos]
  by_cases hB : LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T Z = ⊤
  · rw [hB]
    have hpos : ENNReal.ofReal (Real.exp (2 * β * t) / (2 * β)) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity
    rw [ENNReal.top_pow (by norm_num), ENNReal.mul_top hpos]
    exact le_top
  · have hjoint : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
        ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2) :=
      Finset.measurable_sum _ fun i _ =>
        ((((measurable_pi_apply i).comp hZ)).nnnorm.coe_nnreal_ennreal).pow_const 2
    rw [MeasureTheory.lintegral_lintegral_swap (μ := P)
      (ν := volume.restrict (Set.Icc (0 : ℝ) t))
      (f := fun (ω : Ω) (s : ℝ) => ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2) hjoint.aemeasurable]
    calc ∫⁻ s in Set.Icc (0 : ℝ) t, (∫⁻ ω, ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ∂volume
        ≤ ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (Real.exp (2 * β * s))
            * (LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T Z) ^ (2 : ℕ) ∂volume :=
          MeasureTheory.setLIntegral_mono' measurableSet_Icc fun s hs =>
            LevyStochCalc.Ito.Picard.lintegral_sq_le_bieleckiNorm_sq_weighted β T Z ⟨hs.1, hs.2.trans ht.2⟩
      _ = (∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (Real.exp (2 * β * s)) ∂volume)
            * (LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T Z) ^ (2 : ℕ) :=
          MeasureTheory.lintegral_mul_const' _ _ (by simp [hB, ENNReal.pow_eq_top_iff])
      _ ≤ ENNReal.ofReal (Real.exp (2 * β * t) / (2 * β))
            * (LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T Z) ^ (2 : ℕ) := mul_le_mul' hexp le_rfl
end Weighting

end LevyStochCalc.Ito.Picard


