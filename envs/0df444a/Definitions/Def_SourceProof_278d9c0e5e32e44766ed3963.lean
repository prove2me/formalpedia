-- Prove2me | Definitions.Def_SourceProof_278d9c0e5e32e44766ed3963
-- name    : SourceProof_278d9c0e5e32e44766ed3963
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:13:53.231697+00:00
-- url     : https://prove2.me/theorems/3658da28-bf57-46bb-b4d9-f51992f401ea
-- title:
--   LevyStochCalc source module: SourceProof_278d9c0e5e32e44766ed3963
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral_congr_ae` comes from the `LevyStochCalc.Brownian.MultidimItoCongr` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_MultidimIto_F000
import Definitions.Def_SourceProof_c2510fef121a9f6103ef8e5e

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The multidimensional Itô integral depends only on the class of its integrand

The multidimensional Itô integral is the sum over the coordinates of the one-dimensional
integrals against the coordinate Brownian motions, and each of those depends only on the
almost-everywhere class of its integrand on the window. Two vector integrands agreeing for almost
every time of a window, at almost every sample point, therefore have almost surely equal
multidimensional integrals at the end of that window.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian.Multidim
namespace MultidimBrownianMotion

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
  (W : MultidimBrownianMotion P d) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : ∀ i : Fin d, IsBrownianFiltration (W.W i) ℱ)
  {Z₁ Z₂ : ℝ → Ω → (Fin d → ℝ)}


theorem _root_.Prove2MeSourceProof.h_278d9c0e5e32e44766ed3963
    (hm₁ : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z₁ s ω i))
    (hp₁ : ∀ i : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Z₁ s ω i)
    (hq₁ : ∀ i : Fin d, ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖Z₁ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z₂ s ω i))
    (hp₂ : ∀ i : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Z₂ s ω i)
    (hq₂ : ∀ i : Fin d, ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖Z₂ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T)
    (hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂volume.restrict (Set.Icc (0 : ℝ) T), Z₁ s ω = Z₂ s ω) :
    stochasticIntegral W ℱ hℱ Z₁ hm₁ hp₁ hq₁ T
      =ᵐ[P] stochasticIntegral W ℱ hℱ Z₂ hm₂ hp₂ hq₂ T := by
  have hcomp : ∀ i : Fin d, ∀ᵐ ω ∂P,
      LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W i) ℱ (hℱ i)
          (fun ω' s => Z₁ s ω' i) (hm₁ i) (hp₁ i) (hq₁ i) T ω
        = LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W i) ℱ (hℱ i)
          (fun ω' s => Z₂ s ω' i) (hm₂ i) (hp₂ i) (hq₂ i) T ω := by
    intro i
    refine _root_.Prove2MeSourceProof.h_c2510fef121a9f6103ef8e5e (W.W i) ℱ (hℱ i)
      (hm₁ i) (hp₁ i) (hq₁ i) (hm₂ i) (hp₂ i) (hq₂ i) hT ?_
    filter_upwards [hae] with ω hω
    filter_upwards [hω] with s hs
    rw [hs]
  filter_upwards [Filter.eventually_all.2 hcomp] with ω hω
  exact Finset.sum_congr rfl fun i _ => hω i
end MultidimBrownianMotion
end LevyStochCalc.Brownian.Multidim


