-- Prove2me | Definitions.Def_SourceProof_231d4b01442d4e78331883f1
-- name    : SourceProof_231d4b01442d4e78331883f1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:45:53.387054+00:00
-- url     : https://prove2.me/theorems/17833a8a-2e40-41ec-a14e-0e7283670b8e
-- title:
--   LevyStochCalc source module: SourceProof_231d4b01442d4e78331883f1
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpSplitting.ae_forall_eq_of_ae_rat` comes from the `LevyStochCalc.Ito.JumpSplittingAllTimes` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpSplittingAllTimes_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The finite-activity splitting at all nonnegative times

The finite-activity splitting of a jump diffusion is an identity between the path, a vector Itô
process and a pathwise jump sum, valid almost surely at each fixed nonnegative time. The jump sum
over `(0, t]` is right-continuous in `t` on a window carrying an integrable jump coefficient and a
jump diffusion has almost surely càdlàg paths, so the identity extends from the nonnegative
rationals to all of `[0, ∞)` on a single set of full measure, for any modification of the vector
Itô process whose paths are right-continuous.

## Main statements

* `LevyStochCalc.Ito.JumpSplitting.tendsto_jumpSum_nhdsWithin_Ioi` — right-continuity in time of
  the pathwise jump sum.
* `LevyStochCalc.Ito.JumpSplitting.ae_forall_eq_of_ae_rat` — two almost surely right-continuous
  processes agreeing almost surely at each nonnegative rational time agree almost surely at every
  nonnegative time.
* `LevyStochCalc.Ito.JumpSplitting.ae_forall_eq_add_jumpSum` — the finite-activity splitting,
  almost surely at all nonnegative times simultaneously.
* `LevyStochCalc.Ito.JumpSplitting.jumpSum_eq_of_measure_zero` — the jump sum is constant across a
  window carrying no mass of the random measure.
* `LevyStochCalc.Ito.JumpSplitting.add_shift_eq_of_ae_forall` — the splitting written as a path
  translated by a shift held fixed strictly between consecutive members of a chain of times.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §6.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §IV.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpSplitting

universe u v

section Rationals

end Rationals

section Upgrade

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}


theorem _root_.Prove2MeSourceProof.h_231d4b01442d4e78331883f1 {Y Z : ℝ → Ω → ℝ}
    (hrat : ∀ q : ℚ, 0 ≤ (q : ℝ) → ∀ᵐ ω ∂P, Y (q : ℝ) ω = Z (q : ℝ) ω)
    (hY : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y t ω)))
    (hZ : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Filter.Tendsto (fun s => Z s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Z t ω))) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → Y t ω = Z t ω := by
  have hall : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 ≤ (q : ℝ) → Y (q : ℝ) ω = Z (q : ℝ) ω := by
    refine MeasureTheory.ae_all_iff.mpr fun q => ?_
    by_cases hq : 0 ≤ (q : ℝ)
    · filter_upwards [hrat q hq] with ω hω
      exact fun _ => hω
    · exact Filter.Eventually.of_forall fun ω h => absurd h hq
  filter_upwards [hall, hY, hZ] with ω hω hYω hZω
  intro t ht
  obtain ⟨u, hgt, hu⟩ := LevyStochCalc.Ito.JumpSplitting.exists_seq_rat_gt t
  have hin : Filter.Tendsto (fun m => ((u m : ℚ) : ℝ)) Filter.atTop
      (nhdsWithin t (Set.Ioi t)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hu
      (Filter.Eventually.of_forall hgt)
  refine tendsto_nhds_unique (Filter.Tendsto.congr ?_ ((hYω t ht).comp hin))
    ((hZω t ht).comp hin)
  intro m
  exact hω (u m) (le_trans ht (hgt m).le)
end Upgrade

section Setup

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

section AllTimes

variable (X : Setting.JumpDiffusion W N coeffs x₀) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
  (hσm : ∀ (i : Fin n) (j : Fin d),
    Measurable (Function.uncurry fun ω s => coeffs.σ s (X.X s ω) i j))
  (hσp : ∀ (i : Fin n) (j : Fin d),
    Probability.ProgressivelyMeasurable ℱ fun ω s => coeffs.σ s (X.X s ω) i j)
  (hσq : ∀ (i : Fin n) (j : Fin d) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.σ s (X.X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
  (hγm : ∀ i : Fin n,
    Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X.X p.2.1 p.1) p.2.2 i)
  (hγp : ∀ i : Fin n,
    Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => coeffs.γ s (X.X s ω) e i)
  (hγq : ∀ (i : Fin n) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s (X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

end AllTimes

end Setup

end LevyStochCalc.Ito.JumpSplitting


