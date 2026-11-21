-- Prove2me | Definitions.Def_SourceProof_0daa29c859deac993b505738
-- name    : SourceProof_0daa29c859deac993b505738
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:42:41.846176+00:00
-- url     : https://prove2.me/theorems/0b89c7c7-16c2-434c-be63-760594fd61c0
-- title:
--   LevyStochCalc source module: SourceProof_0daa29c859deac993b505738
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpSplitting.tendsto_jumpSum_nhdsWithin_Ioi` comes from the `LevyStochCalc.Ito.JumpSplittingAllTimes` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpSplittingAllTimes_F001

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

end Upgrade

section Setup

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}


theorem _root_.Prove2MeSourceProof.h_0daa29c859deac993b505738 (X : Setting.JumpDiffusion W N coeffs x₀) {A : Set E}
    (hA : MeasurableSet A) {i : Fin n}
    (hγm : Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X.X p.2.1 p.1) p.2.2 i) {ω : Ω}
    (hint : ∀ T : ℝ, IntegrableOn (fun q : ℝ × E => coeffs.γ q.1 (X.X q.1 ω) q.2 i)
      (Set.Ioc (0 : ℝ) T ×ˢ A) (N.N ω)) (t : ℝ) :
    Filter.Tendsto (fun s => jumpSum X A s ω i) (nhdsWithin t (Set.Ioi t))
      (nhds (jumpSum X A t ω i)) := by
  have hfm : Measurable fun q : ℝ × E => coeffs.γ q.1 (X.X q.1 ω) q.2 i :=
    hγm.comp measurable_prodMk_left
  simp only [LevyStochCalc.Ito.JumpSplitting.jumpSum_eq_integral_indicator X hA]
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    ((Set.Ioc (0 : ℝ) (t + 1) ×ˢ A).indicator
      fun q : ℝ × E => ‖coeffs.γ q.1 (X.X q.1 ω) q.2 i‖) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun s =>
      (hfm.indicator (measurableSet_Ioc.prod hA)).aestronglyMeasurable
  · filter_upwards [(ge_mem_nhds (lt_add_one t)).filter_mono nhdsWithin_le_nhds] with s hs
    refine Filter.Eventually.of_forall fun q => ?_
    by_cases hq : q ∈ Set.Ioc (0 : ℝ) s ×ˢ A
    · have hq' : q ∈ Set.Ioc (0 : ℝ) (t + 1) ×ˢ A := ⟨⟨hq.1.1, hq.1.2.trans hs⟩, hq.2⟩
      simp [Set.indicator_of_mem hq, Set.indicator_of_mem hq']
    · have hnn : (0 : ℝ) ≤ (Set.Ioc (0 : ℝ) (t + 1) ×ˢ A).indicator
          (fun q : ℝ × E => ‖coeffs.γ q.1 (X.X q.1 ω) q.2 i‖) q :=
        Set.indicator_nonneg (fun _ _ => norm_nonneg _) q
      rw [Set.indicator_of_notMem hq]
      simpa using hnn
  · exact (MeasureTheory.integrable_indicator_iff (measurableSet_Ioc.prod hA)).mpr
      (hint (t + 1)).norm
  · refine Filter.Eventually.of_forall fun q => ?_
    have key : ∀ᶠ s in nhdsWithin t (Set.Ioi t),
        (Set.Ioc (0 : ℝ) t ×ˢ A).indicator
            (fun q : ℝ × E => coeffs.γ q.1 (X.X q.1 ω) q.2 i) q
          = (Set.Ioc (0 : ℝ) s ×ˢ A).indicator
            (fun q : ℝ × E => coeffs.γ q.1 (X.X q.1 ω) q.2 i) q := by
      by_cases hqA : q.2 ∈ A
      · by_cases hq0 : 0 < q.1
        · by_cases hqt : q.1 ≤ t
          · filter_upwards [eventually_mem_nhdsWithin] with s hs
            have h1 : q ∈ Set.Ioc (0 : ℝ) s ×ˢ A := ⟨⟨hq0, hqt.trans (le_of_lt hs)⟩, hqA⟩
            have h2 : q ∈ Set.Ioc (0 : ℝ) t ×ˢ A := ⟨⟨hq0, hqt⟩, hqA⟩
            rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2]
          · have ht' : t < q.1 := not_le.mp hqt
            filter_upwards [(gt_mem_nhds ht').filter_mono nhdsWithin_le_nhds] with s hs
            have h1 : q ∉ Set.Ioc (0 : ℝ) s ×ˢ A := fun hmem => absurd hmem.1.2 (not_le.mpr hs)
            have h2 : q ∉ Set.Ioc (0 : ℝ) t ×ˢ A := fun hmem => absurd hmem.1.2 (not_le.mpr ht')
            rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
        · refine Filter.Eventually.of_forall fun s => ?_
          have h1 : q ∉ Set.Ioc (0 : ℝ) s ×ˢ A := fun hmem => hq0 hmem.1.1
          have h2 : q ∉ Set.Ioc (0 : ℝ) t ×ˢ A := fun hmem => hq0 hmem.1.1
          rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
      · refine Filter.Eventually.of_forall fun s => ?_
        have h1 : q ∉ Set.Ioc (0 : ℝ) s ×ˢ A := fun hmem => hqA hmem.2
        have h2 : q ∉ Set.Ioc (0 : ℝ) t ×ˢ A := fun hmem => hqA hmem.2
        rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
    exact Filter.Tendsto.congr' key tendsto_const_nhds
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


