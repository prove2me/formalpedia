-- Prove2me | Definitions.Def_LevyStochCalc_Ito_TruncatedContinuousPart_F000
-- name    : LevyStochCalc_Ito_TruncatedContinuousPart_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T10:02:37.39501+00:00
-- url     : https://prove2.me/theorems/b9d501f8-cea6-4183-9ec3-0ab80d2f5826
-- title:
--   Source declarations: LevyStochCalc.Ito.TruncatedContinuousPart
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.TruncatedContinuousPart. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpCoefficientPredictableZeroExt_F000
import Definitions.Def_LevyStochCalc_Ito_JumpCoefficientPredictableZeroExt_F001
import Definitions.Def_LevyStochCalc_Ito_VectorItoVersionLimit_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The continuous part of a path with the jumps of a mark set removed

Subtracting from the drift of a coefficient bundle the compensator, over a mark set of finite
intensity, of the jump coefficient read at the left limits of a path leaves a drift that is
jointly measurable, progressively measurable and square-integrable on every bounded window. With
the diffusion coefficient along the path it therefore builds a vector Itô process, and that
process has a continuous adapted version: the continuous part to which the finite-activity
splitting adds the left-limit jump sum.

## Main statements

* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.ae_forall_coord_eq`,
  `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.ae_forall_tendsto_nhdsGT` — the coordinatewise
  and right-continuity forms of a continuous adapted version.
* `LevyStochCalc.Ito.JumpSplitting.measurable_uncurry_continuousDriftLeftAt`,
  `LevyStochCalc.Ito.JumpSplitting.progressivelyMeasurable_continuousDriftLeftAt`,
  `LevyStochCalc.Ito.JumpSplitting.lintegral_sq_continuousDriftLeftAt_lt_top` — the drift
  carrying the left-limit compensator is an admissible Itô drift.
* `LevyStochCalc.Ito.JumpSplitting.exists_continuousPart` — a continuous adapted version of the
  vector Itô process built from that drift and the diffusion coefficient along the path.
* `LevyStochCalc.Ito.BigJump.ae_forall_bigJumpPath_eq_add_jumpSumLeftAt` — the path with the
  jumps of a mark set removed is its continuous part plus the jump sum over the complement.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §6.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §IV.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian.Ito

open LevyStochCalc.Brownian.Multidim

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {W : Multidim.MultidimBrownianMotion P d}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ}
  {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {hHm : ∀ m k, Measurable (Function.uncurry (H m k))}
  {hHp : ∀ m k, Probability.ProgressivelyMeasurable ℱ (H m k)}
  {hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {V : ℝ → Ω → Fin n → ℝ}

/-- A continuous adapted version of a vector Itô process agrees with it coordinatewise, almost
surely at each nonnegative time. -/
theorem IsVectorItoVersion.ae_forall_coord_eq
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift V) (t : ℝ) (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, ∀ m : Fin n,
      V t ω m = vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift t ω m := by
  filter_upwards [h.ae_eq t ht] with ω hω
  exact fun m => congrFun hω m
/-- Every coordinate of every path of a continuous adapted version of a vector Itô process is
right-continuous. -/
theorem IsVectorItoVersion.ae_forall_tendsto_nhdsGT
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift V) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ m : Fin n,
      Tendsto (fun s => V s ω m) (𝓝[>] t) (𝓝 (V t ω m)) :=
  Filter.Eventually.of_forall fun ω t _ m =>
    (((continuous_apply m).comp (h.continuous_path ω)).tendsto t).mono_left nhdsWithin_le_nhds
end LevyStochCalc.Brownian.Ito

namespace LevyStochCalc.Ito.JumpSplitting

universe u v

section Drift

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {n d : ℕ} {coeffs : Setting.JumpDiffusionCoeffs n d E} {Xp : ℝ → Ω → Fin n → ℝ}

/-- The integral over a mark set of a jointly measurable marked process is strongly measurable in
the sample point and the time. -/
theorem stronglyMeasurable_setIntegral_mark (A : Set E) (f : Ω → ℝ → E → ℝ)
    (hf : Measurable fun p : Ω × ℝ × E => f p.1 p.2.1 p.2.2) :
    StronglyMeasurable fun p : Ω × ℝ => ∫ e in A, f p.1 p.2 e ∂ν :=
  (hf.comp MeasurableEquiv.prodAssoc.measurable).stronglyMeasurable.integral_prod_right'
    (ν := ν.restrict A)
end Drift

section ContinuousPart

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {n d : ℕ} {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}
  {X : Setting.JumpDiffusion W N coeffs x₀}

end ContinuousPart

end LevyStochCalc.Ito.JumpSplitting

namespace LevyStochCalc.Ito.BigJump

open LevyStochCalc.Ito.Setting LevyStochCalc.Ito.SmallJump LevyStochCalc.Ito.JumpSplitting
open LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {n d : ℕ} {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ} {X : JumpDiffusion W N coeffs x₀}

end LevyStochCalc.Ito.BigJump


