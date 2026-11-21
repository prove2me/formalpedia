-- Prove2me | Definitions.Def_SourceProof_57cbaf3ebcd16877e9db5e1f
-- name    : SourceProof_57cbaf3ebcd16877e9db5e1f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T09:07:55.81306+00:00
-- url     : https://prove2.me/theorems/ef90255b-630c-45ea-9084-8a9481bfbc0b
-- title:
--   LevyStochCalc source module: SourceProof_57cbaf3ebcd16877e9db5e1f
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.simpleIntegral_lintegral_sq_finite_brownian` comes from the `LevyStochCalc.Brownian.ItoL2CompletionLp` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoSimpleIsometry_F001
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Process.Adapted

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: `L²` lift of the simple-integrand integral

Lifts `simpleIntegral W H T` into `Lp ℝ 2 P` for an adapted `SimplePredictable`
integrand `H`, shows that this lift is Cauchy along an `L²`-dense approximating
sequence of simple predictable integrands, and identifies the squared `L²`-norm of
the resulting limit `itoIntegralLp_brownian` with the time-space integral
`∫⁻ ω, ∫⁻ s in [0, T], ‖H ω s‖₊² ∂volume ∂P`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]


theorem _root_.Prove2MeSourceProof.h_57cbaf3ebcd16877e9db5e1f
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (hT : 0 < T) (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i)) :
    ∫⁻ ω, (‖simpleIntegral W H T ω‖₊ : ℝ≥0∞) ^ 2 ∂P < ⊤ := by
  rw [LevyStochCalc.Brownian.Ito.simpleIntegral_isometry W ℱ hℱ hT H h_adapt]
  rw [_root_.Prove2MeSourceProof.h_a036b8f875718d55409e7876 H]
  refine ENNReal.sum_lt_top.mpr (fun i _ => ?_)
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  obtain ⟨M, hM⟩ := H.ξ_bounded i
  have h_M_nn : 0 ≤ max M 0 := le_max_right _ _
  have h_bound : ∀ ω, |H.ξ i ω| ≤ max M 0 :=
    fun ω => le_trans (hM ω) (le_max_left _ _)
  have h_norm_le : ∀ ω, (‖H.ξ i ω‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal (max M 0) := by
    intro ω
    rw [show (‖H.ξ i ω‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖H.ξ i ω‖
          from (ofReal_norm _).symm]
    exact ENNReal.ofReal_le_ofReal
      (Real.norm_eq_abs _ ▸ h_bound ω)
  calc ∫⁻ ω, (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ∫⁻ _ω, (ENNReal.ofReal (max M 0)) ^ 2 ∂P := by
        refine MeasureTheory.lintegral_mono (fun ω => ?_)
        exact pow_le_pow_left' (h_norm_le ω) 2
    _ = (ENNReal.ofReal (max M 0)) ^ 2 * P Set.univ := by
        rw [MeasureTheory.lintegral_const]
    _ < ⊤ := by
        rw [MeasureTheory.measure_univ, mul_one]
        exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top
end LevyStochCalc.Brownian.Ito


