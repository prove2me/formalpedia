-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpSplittingRemainderVanishing_F000
-- name    : LevyStochCalc_Ito_JumpSplittingRemainderVanishing_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:13:52.677615+00:00
-- url     : https://prove2.me/theorems/7e1dcd7a-2643-4344-a266-c9de2378eb3f
-- title:
--   LevyStochCalc source module: LevyStochCalc.Ito.JumpSplittingRemainderVanishing
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.Ito.JumpSplittingRemainderVanishing in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_StochasticIntegralLimit_F000
import Definitions.Def_LevyStochCalc_Ito_StochasticIntegralLimit_F001
import Definitions.Def_LevyStochCalc_Ito_StochasticIntegralLimit_F002
import Definitions.Def_LevyStochCalc_Ito_StochasticIntegralLimit_F004
import Definitions.Def_SourceProof_c1b36e8cddd2b346f7818b69
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.PiSystem
import Mathlib.Topology.Algebra.Order.Floor

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Vanishing remainders and the jump of a solution

Along a subsequence of the spanning sets of the intensity the compensated integrals of a finite
family of integrands cut to the complements of those sets vanish uniformly on every bounded
window, by Doob's `L²` maximal inequality against the Itô–Lévy isometry; passing to such a
subsequence in the splitting with remainder, the jump of a jump diffusion across an arrival time
carrying a mark of a spanning set is exactly the jump coefficient read at the left limit there.

## Main statements

* `LevyStochCalc.Ito.JumpSplitting.ae_exists_atomEnum_jump_eq_gamma_of_sdeData` — the jump of a
  solution across an arrival time.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, Theorem 4.4.7, step (II).
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.3.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.JumpSplitting

open LevyStochCalc.Poisson.Compensated

universe u v

section Uniform

open LevyStochCalc.Probability

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

include hℱ in
/-- The second moment at the horizon of the compensated integral of an integrand cut to the
complement of a spanning set of the intensity tends to zero along the spanning sequence. -/
theorem tendsto_lintegral_sq_stochasticIntegral_markCut_spanningSets_compl {T : ℝ}
    (hT : 0 < T) :
    Tendsto (fun m => ∫⁻ ω, (‖stochasticIntegral N ℱ hℱ (markCut (spanningSets ν m)ᶜ φ)
        (measurable_markCut h_meas (measurableSet_spanningSets ν m).compl)
        ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b h_progMeas) (measurableSet_spanningSets ν m).compl)
        (fun T' hT' => sq_markCut h_sq (spanningSets ν m)ᶜ T' hT') T ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      atTop (𝓝 0) := by
  have hanti : Antitone fun m => (spanningSets ν m)ᶜ :=
    fun a b hab => Set.compl_subset_compl.mpr (monotone_spanningSets ν hab)
  have hnull : ν (⋂ m, (spanningSets ν m)ᶜ) = 0 := by
    rw [← Set.compl_iUnion, iUnion_spanningSets, Set.compl_univ, measure_empty]
  have h :=
    IntegralLimit.tendsto_lintegral_sq_stochasticIntegral_markCut_compl_of_antitone
    N ℱ hℱ φ h_meas h_progMeas h_sq (fun m => (spanningSets ν m)ᶜ)
    (fun m => (measurableSet_spanningSets ν m).compl) hanti hnull hT
  refine h.congr fun m => lintegral_congr_ae ?_
  filter_upwards [_root_.Prove2MeSourceProof.h_c1b36e8cddd2b346f7818b69 N ℱ hℱ φ h_meas
    h_progMeas h_sq (measurableSet_spanningSets ν m) T] with ω hω
  have hcc : markCut (spanningSets ν m)ᶜᶜ φ = markCut (spanningSets ν m) φ := by
    rw [compl_compl]
  simp only [compl_compl, hω, sub_add_cancel_left, nnnorm_neg]
end Uniform

section Solution

open LevyStochCalc.Brownian.Ito

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {n d : ℕ} {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}
  {X : Setting.JumpDiffusion W N coeffs x₀}

end Solution

end LevyStochCalc.Ito.JumpSplitting


