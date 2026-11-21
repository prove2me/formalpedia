-- Prove2me | Definitions.Def_SourceProof_f66d6db4e190cceae9d19c65
-- name    : SourceProof_f66d6db4e190cceae9d19c65
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T09:13:52.258561+00:00
-- url     : https://prove2.me/theorems/f21dc73b-3346-4d3c-97b0-e0a5db2cdaba
-- title:
--   LevyStochCalc source module: SourceProof_f66d6db4e190cceae9d19c65
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.simpleIntegral_memLp_brownian` comes from the `LevyStochCalc.Brownian.ItoL2CompletionLp` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_57cbaf3ebcd16877e9db5e1f

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


theorem _root_.Prove2MeSourceProof.h_f66d6db4e190cceae9d19c65
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (hT : 0 < T) (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i)) :
    MeasureTheory.MemLp (fun ω => simpleIntegral W H T ω) 2 P := by
  refine ⟨?_, ?_⟩
  · -- AEStronglyMeasurable: simpleIntegral W H T = ∑_i ξ_i · ΔW_i
    -- is a finite sum of products of measurable functions.
    refine Measurable.aestronglyMeasurable ?_
    unfold LevyStochCalc.Brownian.Ito.simpleIntegral
    refine Finset.measurable_sum _ (fun i _ => ?_)
    refine Measurable.mul (H.ξ_measurable i) ?_
    exact (W.measurable_eval _).sub (W.measurable_eval _)
  · -- eLpNorm < ⊤: from C0b.10-pre1 (∫⁻ ‖simpleIntegral‖² < ⊤) via
    -- eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top.
    rw [MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by simp : (2 : ℝ≥0∞) ≠ ⊤)]
    have h_two_toReal : (2 : ℝ≥0∞).toReal = 2 := by simp
    rw [h_two_toReal]
    have h_pre := _root_.Prove2MeSourceProof.h_57cbaf3ebcd16877e9db5e1f W ℱ hℱ hT H h_adapt
    -- Bridge ‖x‖ₑ ^ (2:ℝ) vs (‖x‖₊ : ℝ≥0∞) ^ (2:ℕ)
    have h_rewrite : ∀ ω : Ω,
        (‖LevyStochCalc.Brownian.Ito.simpleIntegral W H T ω‖ₑ : ℝ≥0∞) ^ (2 : ℝ)
          = (‖LevyStochCalc.Brownian.Ito.simpleIntegral W H T ω‖₊ : ℝ≥0∞) ^ 2 := by
      intro ω
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
      rfl
    rw [show (fun ω => (‖LevyStochCalc.Brownian.Ito.simpleIntegral W H T ω‖ₑ : ℝ≥0∞) ^ (2 : ℝ))
          = (fun ω => (‖LevyStochCalc.Brownian.Ito.simpleIntegral W H T ω‖₊ : ℝ≥0∞) ^ 2) from
        funext h_rewrite]
    exact h_pre
end LevyStochCalc.Brownian.Ito


