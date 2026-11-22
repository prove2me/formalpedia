-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpSplittingPathSums_F001
-- name    : LevyStochCalc_Ito_JumpSplittingPathSums_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T09:09:30.092809+00:00
-- url     : https://prove2.me/theorems/126034b1-78e7-4164-9d99-223e45ae31eb
-- title:
--   Source declarations: LevyStochCalc.Ito.JumpSplittingPathSums
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.JumpSplittingPathSums. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpSplittingPathSums_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Pathwise left-limit jump sums and compensator drifts

A pathwise jump sum is an integral against the random measure of a jump coefficient read along
the left limits of a path, so it is determined by a coefficient bundle, a random measure and a
path; no relation between the bundle and the path enters. This file indexes the left limits, the
left-limit jump sum over a mark set and the drift carrying the left-limit compensator on such a
triple, identifies them along the path of a jump diffusion with the jump-diffusion-indexed
objects, and records their elementary regularity: the jump sum vanishes over the degenerate
window, the jump sum and the compensator drift are unchanged when the left-limit jump integrand
is replaced by its zero extension, a càdlàg path meets its left limits at all but countably many
positive times, the jump sum is right-continuous in time, its integrand is almost surely
integrable over every bounded window of a mark set of finite intensity, and both the jump sum and
the compensator drift depend on the coefficient bundle only through the values of its jump
coefficient on that mark set.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.JumpSplitting

universe u v

section Setup

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}

section BarePath

variable {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

end BarePath

section BareRegularity

variable (coeffs : Setting.JumpDiffusionCoeffs n d E)
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (Xp : ℝ → Ω → Fin n → ℝ)

variable {Xp}

variable (Xp)

omit [MeasurableSpace E] in
/-- The Brownian integral of a row of the diffusion coefficient along a path is the martingale
part of the corresponding coordinate of the vector Itô process built from it. -/
theorem multidimIntegral_eq_vectorItoMartingaleAt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hσm : ∀ (i : Fin n) (j : Fin d),
      Measurable (Function.uncurry fun ω s => coeffs.σ s (Xp s ω) i j))
    (hσp : ∀ (i : Fin n) (j : Fin d),
      Probability.ProgressivelyMeasurable ℱ fun ω s => coeffs.σ s (Xp s ω) i j)
    (hσq : ∀ (i : Fin n) (j : Fin d) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (Xp s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (i : Fin n) (t : ℝ) (ω : Ω) :
    LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱW
        (fun s ω => coeffs.σ s (Xp s ω) i) (fun j => hσm i j) (fun j => hσp i j)
        (fun j => hσq i j) t ω
      = LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hℱW
          (fun i j ω s => coeffs.σ s (Xp s ω) i j) hσm hσp hσq i t ω := rfl
end BareRegularity

section Bundles

/-- Two coefficient bundles whose jump coefficients agree on a mark set have the same jump sum
over that mark set. -/
theorem jumpSumLeftAt_congr_of_eqOn (coeffs coeffs' : Setting.JumpDiffusionCoeffs n d E)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (Xp : ℝ → Ω → Fin n → ℝ) {A : Set E}
    (hA : MeasurableSet A)
    (hγ : ∀ (s : ℝ) (y : Fin n → ℝ) (e : E), e ∈ A → coeffs'.γ s y e = coeffs.γ s y e)
    (t : ℝ) (ω : Ω) (i : Fin n) :
    jumpSumLeftAt coeffs' N Xp A t ω i = jumpSumLeftAt coeffs N Xp A t ω i :=
  setIntegral_congr_fun (measurableSet_Ioc.prod hA) fun q hq =>
    congrFun (hγ q.1 (leftLimPathAt Xp q.1 ω) q.2 hq.2) i
omit [MeasurableSpace Ω] [SigmaFinite ν] in
/-- Two coefficient bundles with the same drift whose jump coefficients agree on a mark set have
the same drift carrying the left-limit compensator over that mark set. -/
theorem continuousDriftLeftAt_congr_of_eqOn (coeffs coeffs' : Setting.JumpDiffusionCoeffs n d E)
    (Xp : ℝ → Ω → Fin n → ℝ) {A : Set E} (hA : MeasurableSet A) (hμ : coeffs'.μ = coeffs.μ)
    (hγ : ∀ (s : ℝ) (y : Fin n → ℝ) (e : E), e ∈ A → coeffs'.γ s y e = coeffs.γ s y e) :
    continuousDriftLeftAt coeffs' ν Xp A = continuousDriftLeftAt coeffs ν Xp A := by
  funext i ω s
  rw [continuousDriftLeftAt, continuousDriftLeftAt, hμ]
  congr 1
  exact setIntegral_congr_fun hA fun e he => congrFun (hγ s (leftLimPathAt Xp s ω) e he) i
end Bundles

end Setup

end LevyStochCalc.Ito.JumpSplitting


