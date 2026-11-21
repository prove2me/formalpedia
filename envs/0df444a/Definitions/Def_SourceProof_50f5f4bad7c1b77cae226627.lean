-- Prove2me | Definitions.Def_SourceProof_50f5f4bad7c1b77cae226627
-- name    : SourceProof_50f5f4bad7c1b77cae226627
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:23:00.313181+00:00
-- url     : https://prove2.me/theorems/7c343626-853f-44e4-b218-0fb56ccfb810
-- title:
--   LevyStochCalc source module: SourceProof_50f5f4bad7c1b77cae226627
-- statement:
--   The original source theorem `LevyStochCalc.Driver.integral_mul_charRe_eq` comes from the `LevyStochCalc.Driver.CellGronwallPairing` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_CellGronwallPairing_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The pairings of a weight with the cell character

The mixed cell lemma runs a Grönwall argument on the pairing of a square-integrable weight and a
bounded factor with the product of the Brownian cell character `e^{i l X_s}` and the Poisson cell
character. That complex pairing is the combination of four real pairings, one for each of the
cosine and sine against the real and imaginary parts of the Poisson character, and equally the
cosine half plus `i` times the sine half, a half being the pairing of a trigonometric function of
the Brownian increment with the Poisson character. This file introduces those pairings together
with their integrability and boundedness, and records the cell identity for a real pairing in the
reduced form that the recombination consumes.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated
open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι]

section Parts

variable (N : PoissonRandomMeasure P ν)

end Parts

section Half

variable (N : PoissonRandomMeasure P ν)

variable {Z V : Ω → ℝ} {Mv l : ℝ} {X : ℝ → Ω → ℝ} {g : ℝ → ℝ}

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in

theorem _root_.Prove2MeSourceProof.h_50f5f4bad7c1b77cae226627 (hℱ : IsPoissonFiltration N ℱ) (w : ι → ℝ)
    {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {T : ℝ}
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) (hZ2 : MemLp Z 2 P) (hVm : Measurable V)
    (hVb : ∀ ω, |V ω| ≤ Mv) (hgc : Continuous g) (hgb : ∀ x, |g x| ≤ 1) {s : ℝ} (hs : 0 < s)
    (hsT : s ≤ T) {e : E} (he : e ∈ A) (hXs : Measurable (X s)) :
    ∫ ω, Z ω * V ω * (g (l * X s ω) * charRe N w Bfam A T ω s e) ∂P
      = (markFactor w Bfam (s, e) * cellHalf N w Bfam Z V l X g s).re := by
  have hr := LevyStochCalc.Driver.integrable_weight (l := l) (X := X) hZ2 hVm hVb hgc hgb hXs
  have hjoint : Measurable fun p : Ω × ℝ × E => LevyStochCalc.Poisson.charIntegrand N w Bfam A T p.1 p.2.1 p.2.2 :=
    (_root_.Prove2MeSourceProof.h_ac442bc7d640aae9c9b7360e N hℱ w hBm hA hAν hBsub).mono
      (LevyStochCalc.Probability.markedPredictableSigma_le ℱ ν) le_rfl
  have hcm : Measurable fun ω => LevyStochCalc.Poisson.charIntegrand N w Bfam A T ω s e :=
    hjoint.comp (measurable_id.prodMk
      (measurable_const : Measurable fun _ : Ω => ((s, e) : ℝ × E)))
  have hint : Integrable (fun ω => ((Z ω * V ω * g (l * X s ω) : ℝ) : ℂ)
      * LevyStochCalc.Poisson.charIntegrand N w Bfam A T ω s e) P := by
    refine (hr.ofReal.bdd_mul (c := 2) hcm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => _root_.Prove2MeSourceProof.h_099fb631e9952e9258da9935 N w Bfam A T ω s e)).congr
      (Filter.Eventually.of_forall fun ω => mul_comm _ _)
  have hstep : ∫ ω, Z ω * V ω * (g (l * X s ω) * LevyStochCalc.Poisson.charRe N w Bfam A T ω s e) ∂P
      = ∫ ω, (((Z ω * V ω * g (l * X s ω) : ℝ) : ℂ)
          * LevyStochCalc.Poisson.charIntegrand N w Bfam A T ω s e).re ∂P := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, LevyStochCalc.Poisson.charRe]
    ring
  have hre : ∫ ω, (((Z ω * V ω * g (l * X s ω) : ℝ) : ℂ)
        * LevyStochCalc.Poisson.charIntegrand N w Bfam A T ω s e).re ∂P
      = (∫ ω, ((Z ω * V ω * g (l * X s ω) : ℝ) : ℂ)
        * LevyStochCalc.Poisson.charIntegrand N w Bfam A T ω s e ∂P).re := integral_re hint
  rw [hstep, hre, LevyStochCalc.Poisson.integral_mul_charIntegrand N w hBm hs hsT he]
  rfl
end Half

section Reduced

variable {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱW : IsBrownianFiltration W ℱ}
  {a b : ℝ}
  {hm : Measurable (Function.uncurry (indIoc Ω a b))}
  {hp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b)}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X : ℝ → Ω → ℝ} {Z V : Ω → ℝ} {Mv l : ℝ}

end Reduced

end LevyStochCalc.Driver


