-- Prove2me | Definitions.Def_SourceProof_4a8d1b971862960ba7ee1fb7
-- name    : SourceProof_4a8d1b971862960ba7ee1fb7
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T12:44:40.757737+00:00
-- url     : https://prove2.me/theorems/41a8fd8a-5f9d-4717-9f5d-26508d895d6c
-- title:
--   LevyStochCalc source module: SourceProof_4a8d1b971862960ba7ee1fb7
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormula.tendsto_mixedCompensatorDriftIntegral_of_tendsto` comes from the `LevyStochCalc.Ito.ItoLevyBoundedDerivsStepsLimits` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsStepsIntegrands_F000
import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsStepsIntegrands_F001
import Definitions.Def_SourceProof_5c5d38cdf193b77dbdd4c35d

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Limit steps of the Itô–Lévy formula at bounded derivatives

Along a family of paths converging to the solution of a jump diffusion at almost every time of a
window, the four term families of the Itô–Lévy formula converge to their counterparts along the
solution: the Brownian integrals of the mixed diffusion integrands and the compensated integrals
of the cut mixed jump increments converge in `L²`, and the mixed drift and compensator-drift
integrals converge almost surely. The compensator-drift step rests on a form of dominated
convergence for a mark integral over a shrinking family of cuts in which the domination and the
pointwise convergence are asked at almost every time of the window only.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Poisson.Compensated LevyStochCalc.Probability

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section DominatedAe

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]

end DominatedAe

section Mixed

open LevyStochCalc.Ito.BigJump LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : MultidimBrownianMotion P d} {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ} {X : JumpDiffusion W N coeffs x₀}
  {u : ℝ → (Fin n → ℝ) → ℝ}


theorem _root_.Prove2MeSourceProof.h_4a8d1b971862960ba7ee1fb7 (S : SdeData X)
    (hu : ContDiff ℝ 2 (Function.uncurry u)) {c : ℝ}
    (hc : ∀ s x i j, |hessian u s x i j| ≤ c) (hc0 : 0 ≤ c) (T : ℝ) (hT : 0 < T)
    (y : ℕ → ℝ → Ω → Fin n → ℝ) (hym : ∀ i, Measurable (Function.uncurry (y i)))
    (ψ : ℕ → ℕ) (hψ : ∀ i, i ≤ ψ i)
    (hpath : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Tendsto (fun i => y i s ω) atTop (𝓝 (X.X s ω))) :
    ∀ᵐ ω ∂P, Tendsto (fun i => ∫ s in Set.Icc (0 : ℝ) T, ∫ e in (smallMarks ν (ψ i))ᶜ,
        mixedCompensatorDriftIntegrand u coeffs.γ s (y i s ω) (X.X s ω) e ∂ν) atTop
      (𝓝 (∫ s in Set.Icc (0 : ℝ) T, ∫ e,
        compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν)) := by
  have hγint : ∀ᵐ ω ∂P, ∀ i : Fin n, Integrable
      (fun p : ℝ × E => coeffs.γ p.1 (X.X p.1 ω) p.2 i ^ 2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν) := by
    refine MeasureTheory.ae_all_iff.mpr fun i => ?_
    filter_upwards [MeasureTheory.ae_lt_top (LevyStochCalc.Poisson.Compensated.measurable_markEnergy
      (f := fun ω s e => (‖LevyStochCalc.Ito.SmallJump.pathJumpCoeff coeffs X.X i ω s e‖₊ : ℝ≥0∞) ^ 2)
      (((S.γ_meas i).nnnorm.coe_nnreal_ennreal).pow_const 2) T) (S.γ_sq i T hT).ne]
      with ω hω
    have hm : Measurable fun p : ℝ × E => coeffs.γ p.1 (X.X p.1 ω) p.2 i :=
      (S.γ_meas i).comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))
    have hfin : ∫⁻ p, (‖coeffs.γ p.1 (X.X p.1 ω) p.2 i‖₊ : ℝ≥0∞) ^ 2
        ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν) < ⊤ := by
      rw [lintegral_prod _ ((hm.nnnorm.coe_nnreal_ennreal.pow_const 2).aemeasurable)]
      exact hω
    exact (LevyStochCalc.Brownian.Ito.memLp_two_of_lintegral_sq_lt_top hm.aestronglyMeasurable hfin).integrable_sq
  filter_upwards [hpath, hγint] with ω hω hγω
  have hγm : Measurable fun p : ℝ × E => coeffs.γ p.1 (X.X p.1 ω) p.2 :=
    measurable_pi_lambda _ fun i =>
      (S.γ_meas i).comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))
  refine _root_.Prove2MeSourceProof.h_5c5d38cdf193b77dbdd4c35d (ν := ν) (T := T)
    (A := fun i => LevyStochCalc.Ito.JumpFormula.smallMarks ν (ψ i))
    (fs := fun i s e => LevyStochCalc.Ito.JumpFormula.mixedCompensatorDriftIntegrand u coeffs.γ s (y i s ω) (X.X s ω) e)
    (f := fun s e => LevyStochCalc.Ito.JumpFormula.compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e)
    (g := fun s e => (n : ℝ) ^ 2 * c * ((n : ℝ) * ∑ i, coeffs.γ s (X.X s ω) e i ^ 2))
    (fun i => LevyStochCalc.Ito.JumpFormula.measurableSet_smallMarks ν (ψ i))
    (LevyStochCalc.Ito.JumpFormula.ae_eventually_notMem_comp (LevyStochCalc.Ito.JumpFormula.antitone_smallMarks ν) (LevyStochCalc.Ito.JumpFormula.measure_iInter_smallMarks ν) hψ)
    ?_ ?_ ?_ ?_
  · intro i
    refine Measurable.aestronglyMeasurable ?_
    have hy : Measurable fun p : ℝ × E => y i p.1 ω :=
      ((hym i).of_uncurry_right).comp measurable_fst
    change Measurable fun p : ℝ × E =>
      u p.1 (y i p.1 ω + coeffs.γ p.1 (X.X p.1 ω) p.2) - u p.1 (y i p.1 ω)
        - ∑ l, coeffs.γ p.1 (X.X p.1 ω) p.2 l * LevyStochCalc.Ito.JumpFormula.gradient u p.1 (y i p.1 ω) l
    refine Measurable.sub (Measurable.sub ?_ ?_) ?_
    · exact hu.continuous.measurable.comp (measurable_fst.prodMk (hy.add hγm))
    · exact hu.continuous.measurable.comp (measurable_fst.prodMk hy)
    · exact Finset.measurable_sum _ fun l _ => ((measurable_pi_apply l).comp hγm).mul
        ((LevyStochCalc.Ito.JumpFormula.continuous_gradient_uncurry hu l).measurable.comp (measurable_fst.prodMk hy))
  · exact ((integrable_finsetSum _ fun l _ => hγω l).const_mul _).const_mul _
  · intro i
    exact Eventually.of_forall fun s e =>
      LevyStochCalc.Ito.JumpFormula.abs_mixedCompensatorDriftIntegrand_le hu hc hc0 s _ _ e
  · filter_upwards [hω] with s hs e
    exact LevyStochCalc.Ito.JumpFormula.tendsto_mixedCompensatorDriftIntegrand_of_tendsto hu coeffs.γ s _ e hs
end Mixed

end LevyStochCalc.Ito.JumpFormula


