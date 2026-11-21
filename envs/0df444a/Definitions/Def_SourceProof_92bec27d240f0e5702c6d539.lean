-- Prove2me | Definitions.Def_SourceProof_92bec27d240f0e5702c6d539
-- name    : SourceProof_92bec27d240f0e5702c6d539
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:58:39.442121+00:00
-- url     : https://prove2.me/theorems/8643307a-3b01-438b-b416-4eda66167d7b
-- title:
--   LevyStochCalc source module: SourceProof_92bec27d240f0e5702c6d539
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.mul_stochasticIntegralBrownian_indIoc` comes from the `LevyStochCalc.Brownian.ItoPullOut` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoPullOut_F000
import Definitions.Def_SourceProof_f7873a967b51c0099c698616

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Pulling a past weight inside an Itô integral over a window

A bounded `ℱ_a`-measurable weight times the Itô integral of an integrand supported in `(a, b]` is
the Itô integral of the weighted integrand: the weight times the indicator is itself a simple
integrand, so this is associativity against a simple integrand.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section PullOut

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in

theorem _root_.Prove2MeSourceProof.h_92bec27d240f0e5702c6d539 {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {V : Ω → ℝ} (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V)
    (hVa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) V)
    (K : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry K))
    (hp : Probability.ProgressivelyMeasurable ℱ K)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (him : Measurable (Function.uncurry fun ω s => indIoc Ω a b ω s * K ω s))
    (hip : Probability.ProgressivelyMeasurable ℱ fun ω s => indIoc Ω a b ω s * K ω s)
    (hiq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖indIoc Ω a b ω s * K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hvm : Measurable (Function.uncurry fun ω s => V ω * indIoc Ω a b ω s * K ω s))
    (hvp : Probability.ProgressivelyMeasurable ℱ fun ω s => V ω * indIoc Ω a b ω s * K ω s)
    (hvq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖V ω * indIoc Ω a b ω s * K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) :
    (fun ω => V ω * stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => indIoc Ω a b ω s * K ω s) him hip hiq t ω)
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => V ω * indIoc Ω a b ω s * K ω s) hvm hvp hvq t := by
  have hloc := _root_.Prove2MeSourceProof.h_371bbffaec7b2a5d68568212 W ℱ hℱ K hm hp hq ha hab him hip hiq ht
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hpt : ∀ (ω : Ω) (s : ℝ),
        (LevyStochCalc.Brownian.Ito.stepIocMul₀ Ω hab V hVb hVm).eval s ω * K ω s
          = V ω * LevyStochCalc.Brownian.Ito.indIoc Ω 0 b ω s * K ω s := by
      intro ω s; rw [LevyStochCalc.Brownian.Ito.stepIocMul₀_eval]
    have hGeval : (fun ω s => (LevyStochCalc.Brownian.Ito.stepIocMul₀ Ω hab V hVb hVm).eval s ω * K ω s)
        = fun ω s => V ω * LevyStochCalc.Brownian.Ito.indIoc Ω 0 b ω s * K ω s := by
      funext ω s; exact hpt ω s
    have hmm : Measurable (Function.uncurry fun ω s =>
        (LevyStochCalc.Brownian.Ito.stepIocMul₀ Ω hab V hVb hVm).eval s ω * K ω s) := by rw [hGeval]; exact hvm
    have hmp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s =>
        (LevyStochCalc.Brownian.Ito.stepIocMul₀ Ω hab V hVb hVm).eval s ω * K ω s := by rw [hGeval]; exact hvp
    have hmq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(LevyStochCalc.Brownian.Ito.stepIocMul₀ Ω hab V hVb hVm).eval s ω * K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
      intro T hT; simp_rw [hpt]; exact hvq T hT
    have hass := _root_.Prove2MeSourceProof.h_f7873a967b51c0099c698616 W ℱ hℱ
      (LevyStochCalc.Brownian.Ito.stepIocMul₀ Ω hab V hVb hVm) (LevyStochCalc.Brownian.Ito.stepIocMul₀_adapt ℱ hab hVb hVm hVa) K hm hp hq
      hmm hmp hmq ht
    rw [LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_fun W ℱ hℱ hGeval hmm hmp hmq hvm hvp hvq t] at hass
    refine Filter.EventuallyEq.trans ?_ hass
    filter_upwards [hloc] with ω hω
    rw [LevyStochCalc.Brownian.Ito.stepIocMul₀_integralAgainst]
    exact congrArg (fun x => V ω * x) hω
  · have hpt : ∀ (ω : Ω) (s : ℝ),
        (LevyStochCalc.Brownian.Ito.stepIocMul Ω ha' hab V hVb hVm).eval s ω * K ω s
          = V ω * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s * K ω s := by
      intro ω s; rw [LevyStochCalc.Brownian.Ito.stepIocMul_eval]
    have hGeval : (fun ω s => (LevyStochCalc.Brownian.Ito.stepIocMul Ω ha' hab V hVb hVm).eval s ω * K ω s)
        = fun ω s => V ω * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s * K ω s := by
      funext ω s; exact hpt ω s
    have hmm : Measurable (Function.uncurry fun ω s =>
        (LevyStochCalc.Brownian.Ito.stepIocMul Ω ha' hab V hVb hVm).eval s ω * K ω s) := by rw [hGeval]; exact hvm
    have hmp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s =>
        (LevyStochCalc.Brownian.Ito.stepIocMul Ω ha' hab V hVb hVm).eval s ω * K ω s := by rw [hGeval]; exact hvp
    have hmq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(LevyStochCalc.Brownian.Ito.stepIocMul Ω ha' hab V hVb hVm).eval s ω * K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
      intro T hT; simp_rw [hpt]; exact hvq T hT
    have hass := _root_.Prove2MeSourceProof.h_f7873a967b51c0099c698616 W ℱ hℱ
      (LevyStochCalc.Brownian.Ito.stepIocMul Ω ha' hab V hVb hVm) (LevyStochCalc.Brownian.Ito.stepIocMul_adapt ℱ ha' hab hVb hVm hVa) K hm hp hq
      hmm hmp hmq ht
    rw [LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_fun W ℱ hℱ hGeval hmm hmp hmq hvm hvp hvq t] at hass
    refine Filter.EventuallyEq.trans ?_ hass
    filter_upwards [hloc] with ω hω
    rw [LevyStochCalc.Brownian.Ito.stepIocMul_integralAgainst]
    exact congrArg (fun x => V ω * x) hω
end PullOut

end LevyStochCalc.Brownian.Ito


