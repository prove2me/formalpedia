-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpSumIdentity_F001
-- name    : LevyStochCalc_Ito_JumpSumIdentity_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:27:45.611817+00:00
-- url     : https://prove2.me/theorems/3d477489-56c0-4e7f-afd7-de0c9e548ba8
-- title:
--   Source declarations: LevyStochCalc.Ito.JumpSumIdentity
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.JumpSumIdentity. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_JumpTimesEnum_F002
import Definitions.Def_LevyStochCalc_Poisson_JumpTimesEnum_F003
import Definitions.Def_LevyStochCalc_Poisson_JumpTimesEnum_F004
import Definitions.Def_LevyStochCalc_Poisson_PathwiseIdentity_F001
import Definitions.Def_SourceProof_2d73a2b6df3c10b500c2eec5

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The jump sum of a finite-activity window

On a window `(0, T] × A` of finite intensity a Poisson random measure is almost surely a finite
sum of Dirac masses. Integer-valuedness makes each of those masses a natural number and
time-simplicity caps it at one, so the integral of a function against the random measure over the
window is the plain sum of the function's values over a finite set of window points carrying
pairwise distinct times. Those times are exactly the arrival times of the mark set inside the
window, so the sum is indexed by the strictly monotone enumeration of the arrival times, each
paired with the unique mark carried at that time.

Chaining that identity with `LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_eq_pathwise`
writes the jump sum of a predictable integrand `φ` as the Itô–Lévy integral of `φ` plus the
integral of `φ` itself against the reference intensity. That second term is not the compensator
drift of the Itô–Lévy formula: the latter integrates `u (x + γ e) - u x - ∑ i, γ i e * ∂ i u x`,
which differs from `φ = u (x + γ e) - u x` by the first-order term `∑ i, γ i e * ∂ i u x`.

## Main statements

* `LevyStochCalc.Poisson.exists_atomFinset_integral_eq_sum` — the integral over a window whose
  restricted measure is integer-valued and time-simple is a plain finite sum over window points.
* `LevyStochCalc.Poisson.ae_exists_atomEnum_integral_eq_sum` — almost surely that sum is indexed
  by the strictly monotone enumeration of the arrival times in the window.
* `LevyStochCalc.Poisson.ae_exists_atomEnum_sum_eq_stochasticIntegral_add` — almost surely the
  jump sum of a predictable integrand is its Itô–Lévy integral plus its integral against the
  reference intensity.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §2.3, §4.4.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.3.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section AtomMass

variable [MeasurableSingletonClass E] (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

end AtomMass

section AtomFinset

variable [MeasurableSingletonClass E] (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

end AtomFinset

section Enumeration

end Enumeration

section AlmostEverywhere

variable [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

end AlmostEverywhere

section Compensated

variable [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]

/-- **The jump sum as an Itô–Lévy integral plus an intensity term.** Almost surely the sum of a
predictable integrand carried by a window of finite intensity over the atoms of that window is
its Itô–Lévy integral plus its integral against the reference intensity. The second term
integrates the integrand itself, not the compensator drift `u (x + γ) - u x - ∑ i, γ i * ∂ i u`
of the Itô–Lévy formula, which differs from it by the first-order term. -/
theorem ae_exists_atomEnum_sum_eq_stochasticIntegral_add
    (N : PoissonRandomMeasure.{u, v, w} P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : IsPoissonFiltration N ℱ) (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (h_sq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {A : Set E} (hA : MeasurableSet A) (hφpred : Probability.MarkedPredictable ℱ ν φ)
    (hAν : ν A ≠ ⊤) (hsupp : ∀ ω s e, e ∉ A → φ ω s e = 0) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∃ (k : ℕ) (θ : Fin k → ℝ) (ε : Fin k → E), StrictMono θ ∧
      Set.range θ = {u : ℝ | ∃ i : ℕ, jumpTime N A i ω = (u : WithTop ℝ) ∧ 0 < u ∧ u ≤ T} ∧
      (∀ i, θ i ∈ Set.Ioc (0 : ℝ) T ∧ ε i ∈ A) ∧
      ∑ i : Fin k, φ ω (θ i) (ε i)
        = Compensated.stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq T ω
          + ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, φ ω q.1 q.2 ∂(referenceIntensity ν) := by
  filter_upwards [_root_.Prove2MeSourceProof.h_2d73a2b6df3c10b500c2eec5 N A hA hAν T,
    Compensated.stochasticIntegral_ae_eq_pathwise N ℱ hℱ φ h_meas h_progMeas h_sq hA hφpred hAν
      hsupp hT] with ω hω hpath
  obtain ⟨k, θ, ε, hmono, hrange, hmem, hsum⟩ := hω
  have hsum' : ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, φ ω q.1 q.2 ∂(N.N ω)
      = ∑ i : Fin k, φ ω (θ i) (ε i) := hsum fun q => φ ω q.1 q.2
  refine ⟨k, θ, ε, hmono, hrange, hmem, ?_⟩
  rw [hpath, ← hsum']
  ring
end Compensated

end LevyStochCalc.Poisson


