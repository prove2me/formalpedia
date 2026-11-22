-- Prove2me | Definitions.Def_SourceProof_fd28faada52b5036aa04b1f8
-- name    : SourceProof_fd28faada52b5036aa04b1f8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T09:20:01.092252+00:00
-- url     : https://prove2.me/theorems/e8e45973-4c00-4ee6-8ff1-c82362781903
-- title:
--   LevyStochCalc source module: SourceProof_fd28faada52b5036aa04b1f8
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormula.measurable_cappedJumpSumAt_leftLimPath` comes from the `LevyStochCalc.Ito.CappedJumpSumMeasurable` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_CappedJumpSumMeasurable_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Measurability of the capped jump sum

The jumps of a mark set accumulated up to an arrival time capped at the horizon, with the jump
coefficient read at the left limits of the path, form a random vector known at that capped
arrival time. The pathwise jump sum over a window is the integral against the random measure of
the jump coefficient at the left limits, which is a predictable marked process; restricting the
random measure to a window on which its mass is finite everywhere gives an s-finite kernel, and
integrals of jointly measurable integrands against an s-finite kernel are measurable. The jump
sum is therefore progressively measurable in the time and the sample point, and its value at
the capped arrival time — a stopping time — is measurable for the σ-algebra of that stopping
time. Without the pathwise finiteness of the count the same integral is only almost surely equal
to a measurable function, which gives almost-everywhere measurability.

## Main definitions

* `LevyStochCalc.Poisson.windowKernel` — a family of measures restricted to a window and set to
  zero at the sample points where the window carries infinite mass, as a kernel.
* `LevyStochCalc.Ito.JumpFormula.leftLimJumpCoeff` — the jump coefficient at the left limits of
  the path, cut to the positive times up to a horizon, on the sample–time–mark space.

## Main statements

* `LevyStochCalc.Poisson.isSFiniteKernel_windowKernel`,
  `LevyStochCalc.Poisson.measurable_integral_windowKernel`,
  `LevyStochCalc.Poisson.measurable_integral_windowKernel_indicator` — the window kernel is
  s-finite, so integrals of jointly measurable integrands against it are measurable.
* `LevyStochCalc.Ito.JumpFormula.jumpSumAt_leftLimPath_eq_integral_windowKernel` — where the
  window count is finite, the left-limit jump sum is the integral against the window kernel.
* `LevyStochCalc.Ito.JumpFormula.isStronglyProgressive_jumpSumAt_leftLimPath`,
  `LevyStochCalc.Ito.JumpFormula.progressivelyMeasurable_jumpSumAt_leftLimPath` — the
  left-limit jump sum is progressively measurable when the count is finite everywhere.
* `LevyStochCalc.Ito.JumpFormula.measurable_cappedJumpSumAt_leftLimPath` — the capped
  left-limit jump sum is measurable when the count is finite everywhere.
* `LevyStochCalc.Ito.JumpFormula.measurable_cappedJumpSumAt_leftLimPath_of_isStoppingTime` —
  the capped left-limit jump sum is measurable for the σ-algebra of the capped arrival time.
* `LevyStochCalc.Ito.JumpFormula.aemeasurable_cappedJumpSumAt_leftLimPath` — for a mark set of
  finite intensity the capped left-limit jump sum is almost-everywhere measurable.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §2.3, §4.4.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.3.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

section WindowKernel

variable {Ω β : Type*} {m : MeasurableSpace Ω} [MeasurableSpace β]

variable {μ : Ω → Measure β} {R : Set β}
  {hμ : ∀ ⦃s : Set β⦄, MeasurableSet s → Measurable fun ω => μ ω (s ∩ R)}

end WindowKernel

section WindowIndicator

variable {Ω E : Type*} {m : MeasurableSpace Ω} [MeasurableSpace E] {μ : Ω → Measure (ℝ × E)}
  {R : Set (ℝ × E)} {hμ : ∀ ⦃s : Set (ℝ × E)⦄, MeasurableSet s → Measurable fun ω => μ ω (s ∩ R)}

end WindowIndicator

end LevyStochCalc.Poisson

namespace LevyStochCalc.Ito.JumpFormula

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

section Clip

end Clip

section Integrand

variable (X : Setting.JumpDiffusion W N coeffs x₀)

end Integrand

section Progressive

variable (X : Setting.JumpDiffusion W N coeffs x₀) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)

end Progressive

section Capped

variable (X : Setting.JumpDiffusion W N coeffs x₀)
variable {A : Set E}


theorem _root_.Prove2MeSourceProof.h_fd28faada52b5036aa04b1f8 (hA : MeasurableSet A)
    (hfin : ∀ (ω : Ω) (t : ℝ), LevyStochCalc.Poisson.arrivalCount N A t ω ≠ ⊤)
    (hleft : ∀ (ω : Ω) (t : ℝ), 0 < t → ∀ j : Fin n,
      ∃ L : ℝ, Tendsto (fun s => X.X s ω j) (𝓝[<] t) (𝓝 L))
    (hγ : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2) (T : ℝ)
    (k : ℕ) : Measurable (cappedJumpSumAt X (JumpSplitting.leftLimPath X) A T k) := by
  refine measurable_pi_iff.mpr fun i => ?_
  let ℱ₀ : Filtration ℝ ‹MeasurableSpace Ω› := Filtration.const ℝ ‹MeasurableSpace Ω› le_rfl
  have hXadapt₀ : ∀ t : ℝ, Measurable[ℱ₀ t] (X.X t) :=
    fun t => X.measurable_path.comp measurable_prodMk_left
  have hG : Measurable (LevyStochCalc.Ito.JumpFormula.leftLimJumpCoeff X T i) :=
    LevyStochCalc.Ito.JumpFormula.measurable_leftLimJumpCoeff X ℱ₀ hXadapt₀ hleft ((measurable_pi_apply i).comp hγ) T
  have hkey := LevyStochCalc.Poisson.measurable_integral_windowKernel_indicator
    (hμ := LevyStochCalc.Ito.JumpFormula.measurable_count_inter_window' (N := N) hA T) hA hG measurable_id
    (LevyStochCalc.Ito.JumpFormula.measurable_clipTime_jumpTime (N := N) hA T k)
  rw [show (fun ω => LevyStochCalc.Ito.JumpFormula.cappedJumpSumAt X (LevyStochCalc.Ito.JumpSplitting.leftLimPath X) A T k ω i)
    = fun ω => ∫ q, (Set.Ioc (0 : ℝ)
        (LevyStochCalc.Brownian.Ito.clipTime (LevyStochCalc.Poisson.jumpTime N A k) T ω)
          ×ˢ A).indicator (fun q => LevyStochCalc.Ito.JumpFormula.leftLimJumpCoeff X T i (ω, q)) q
      ∂(LevyStochCalc.Poisson.windowKernel N.N (Set.Ioc (0 : ℝ) T ×ˢ A)
        (LevyStochCalc.Ito.JumpFormula.measurable_count_inter_window' hA T) ω)
    from funext fun ω => LevyStochCalc.Ito.JumpFormula.jumpSumAt_leftLimPath_eq_integral_windowKernel X hA ℱ₀
      (LevyStochCalc.Brownian.Ito.clipTime_le_self _ _ _) (hfin ω T) i]
  exact hkey
end Capped

end LevyStochCalc.Ito.JumpFormula


