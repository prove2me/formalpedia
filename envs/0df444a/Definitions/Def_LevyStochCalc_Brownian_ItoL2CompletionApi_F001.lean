-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionApi_F001
-- name    : LevyStochCalc_Brownian_ItoL2CompletionApi_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:28:48.565174+00:00
-- url     : https://prove2.me/theorems/c401ae34-500c-4e18-919f-aae5b349f47b
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoL2CompletionApi
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoL2CompletionApi. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionQuadVar_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionQuadVar_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionQuadVar_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: the `stochasticIntegral` API

The martingale property of the compensated square for the right-continuation `ℱ₊` of `ℱ`,
the unified existence theorem `itoIsometry_brownian_unified_existence` combining the
martingale, quadratic-variation and isometry conclusions, the isometry for differences of
integrands, and the `stochasticIntegral` interface with `itoIsometry`,
`quadVar_stochasticIntegral` and `martingale_stochasticIntegral`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

section MasterSequence

variable
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

end MasterSequence

/-- **Cross-integrand simple difference isometry.** For two integrands `H₁, H₂`, their
`masterApprox n` simple integrals satisfy `∫⁻‖Iₙ(H₁) − Iₙ(H₂)‖² = ∫⁻∫⁻‖evalₙ(H₁) −
evalₙ(H₂)‖²` at every `t ≥ 0`. Both `masterApprox · n` live on horizon `n+1`; extend
each to the common horizon `n+2` via `appendInterval` (which preserves `simpleIntegral`
and `eval`) and apply `simpleIntegral_intermediate_diff_isometry`. -/
theorem masterApprox_cross_diff_isometry
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ) (H₁ H₂ : Ω → ℝ → ℝ)
    (h_meas₁ : Measurable (Function.uncurry H₁)) (h_meas₂ : Measurable (Function.uncurry H₂))
    (h_progMeas₁ : Probability.ProgressivelyMeasurable ℱ H₁)
    (h_progMeas₂ : Probability.ProgressivelyMeasurable ℱ H₂)
    (h_sq₁ : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_sq₂ : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (n : ℕ) {t : ℝ} (ht_nn : 0 ≤ t) :
    ∫⁻ ω, (‖simpleIntegral W (masterApprox ℱ H₁ h_meas₁ h_progMeas₁ h_sq₁ n) t ω
        - simpleIntegral W (masterApprox ℱ H₂ h_meas₂ h_progMeas₂ h_sq₂ n) t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖(masterApprox ℱ H₁ h_meas₁ h_progMeas₁ h_sq₁ n).eval s ω
            - (masterApprox ℱ H₂ h_meas₂ h_progMeas₂ h_sq₂ n).eval s ω‖₊ : ℝ≥0∞) ^ 2
            ∂volume ∂P := by
  set Gn := masterApprox ℱ H₁ h_meas₁ h_progMeas₁ h_sq₁ n with hGn
  set Gm := masterApprox ℱ H₂ h_meas₂ h_progMeas₂ h_sq₂ n with hGm
  have hKn : Gn.partition (Fin.last Gn.N) < (n : ℝ) + 2 := by
    have h1 : Gn.partition (Fin.last Gn.N) ≤ (n : ℝ) + 1 := Gn.partition_le_T
    linarith
  have hKm : Gm.partition (Fin.last Gm.N) < (n : ℝ) + 2 := by
    have h1 : Gm.partition (Fin.last Gm.N) ≤ (n : ℝ) + 1 := Gm.partition_le_T
    linarith
  have h_eq : (Gn.appendInterval hKn).partition (Fin.last (Gn.appendInterval hKn).N)
      = (Gm.appendInterval hKm).partition (Fin.last (Gm.appendInterval hKm).N) :=
    (Gn.appendInterval_partition_last hKn).trans (Gm.appendInterval_partition_last hKm).symm
  have ha_n := Gn.appendInterval_adapt ℱ hKn
    (masterApprox_adapt ℱ H₁ h_meas₁ h_progMeas₁ h_sq₁ n)
  have ha_m := Gm.appendInterval_adapt ℱ hKm
    (masterApprox_adapt ℱ H₂ h_meas₂ h_progMeas₂ h_sq₂ n)
  have hiso := simpleIntegral_intermediate_diff_isometry W ℱ hℱ (Gn.appendInterval hKn)
    (Gm.appendInterval hKm) h_eq ha_n ha_m ht_nn
  have hL : ∫⁻ ω, (‖simpleIntegral W Gn t ω - simpleIntegral W Gm t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, (‖simpleIntegral W (Gn.appendInterval hKn) t ω
          - simpleIntegral W (Gm.appendInterval hKm) t ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    refine lintegral_congr (fun ω => ?_)
    rw [(fun p2mMethodArg0 => _root_.Prove2MeSourceProof.h_c5a0aac77ea3887770fece7e p2mMethodArg0 Gn) W hKn t ω, (fun p2mMethodArg0 => _root_.Prove2MeSourceProof.h_c5a0aac77ea3887770fece7e p2mMethodArg0 Gm) W hKm t ω]
  have hR : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖Gn.eval s ω - Gm.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖(Gn.appendInterval hKn).eval s ω - (Gm.appendInterval hKm).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P := by
    refine lintegral_congr (fun ω => ?_)
    refine MeasureTheory.setLIntegral_congr_fun measurableSet_Icc (fun s _ => ?_)
    rw [(_root_.Prove2MeSourceProof.h_3d4df4df753a663d9a385c25 Gn) hKn s ω, (_root_.Prove2MeSourceProof.h_3d4df4df753a663d9a385c25 Gm) hKm s ω]
  rw [hL, hR]; exact hiso
end LevyStochCalc.Brownian.Ito


