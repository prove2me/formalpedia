-- Prove2me | Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsStepsIntegrands_F000
-- name    : LevyStochCalc_Ito_ItoLevyBoundedDerivsStepsIntegrands_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T12:34:21.863536+00:00
-- url     : https://prove2.me/theorems/89cc452c-c8fa-4d13-813e-829b881c8800
-- title:
--   Source declarations: LevyStochCalc.Ito.ItoLevyBoundedDerivsStepsIntegrands
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.ItoLevyBoundedDerivsStepsIntegrands. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyMixedBounds_F001
import Definitions.Def_LevyStochCalc_Probability_MarkedProgressiveSlice_F000
import Definitions.Def_SourceProof_7ac4f497a1ed78b320395909
import Definitions.Def_SourceProof_c52cb68531741ca4a978b2b1

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Admissibility of the mixed integrands of the Itô–Lévy formula

The mixed integrands of the Itô–Lévy formula along a jump diffusion — the derivatives of a `C²`
state function read at an auxiliary path, the coefficients read at the solution — are jointly
measurable, are progressively measurable for the right-continuous regularisation of the
filtration of the SDE data, and have finite energy on every bounded window; over that
regularisation the Brownian and the compensated jump integral agree almost surely with the ones
over the filtration itself, and the endpoint of a path together with its two stochastic
integrals is measurable componentwise.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Poisson.Compensated LevyStochCalc.Probability

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section Mixed

open LevyStochCalc.Ito.BigJump LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : MultidimBrownianMotion P d} {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ} {X : JumpDiffusion W N coeffs x₀}
  {u : ℝ → (Fin n → ℝ) → ℝ}

/-- The mixed diffusion integrand, read at an auxiliary path and at the solution, is jointly
measurable in the sample point and the time. -/
theorem measurable_uncurry_mixedDiffusionIntegrand (S : SdeData X)
    (hu : ContDiff ℝ 2 (Function.uncurry u)) (y : ℝ → Ω → Fin n → ℝ)
    (hy : Measurable (Function.uncurry y)) (j : Fin d) :
    Measurable (Function.uncurry
      fun ω s => mixedDiffusionIntegrand u coeffs.σ s (y s ω) (X.X s ω) j) := by
  change Measurable fun p : Ω × ℝ =>
    ∑ i, gradient u p.2 (y p.2 p.1) i * coeffs.σ p.2 (X.X p.2 p.1) i j
  refine Finset.measurable_sum _ fun i _ => Measurable.mul ?_ (S.σ_meas i j)
  exact (continuous_gradient_uncurry hu i).measurable.comp
    (measurable_snd.prodMk (hy.comp (measurable_snd.prodMk measurable_fst)))
/-- The mixed diffusion integrand, read at a right-continuous adapted auxiliary path and at the
solution, is progressively measurable for the right-continuous filtration of the SDE data. -/
theorem progressivelyMeasurable_mixedDiffusionIntegrand (S : SdeData X)
    (hu : ContDiff ℝ 2 (Function.uncurry u)) (y : ℝ → Ω → Fin n → ℝ)
    (hyad : ∀ t : ℝ, Measurable[S.ℱ.rightCont t] (y t))
    (hyrc : ∀ (ω : Ω) (t : ℝ), Tendsto (fun s => y s ω) (𝓝[>] t) (𝓝 (y t ω))) (j : Fin d) :
    Probability.ProgressivelyMeasurable S.ℱ.rightCont
      fun ω s => mixedDiffusionIntegrand u coeffs.σ s (y s ω) (X.X s ω) j := by
  change Probability.ProgressivelyMeasurable S.ℱ.rightCont
    fun ω s => ∑ i, gradient u s (y s ω) i * coeffs.σ s (X.X s ω) i j
  refine progressivelyMeasurable_finset_sum _ fun i _ =>
    Probability.ProgressivelyMeasurable.mul ?_
      ((S.σ_prog i j).mono fun t => S.ℱ.le_rightCont t)
  exact _root_.Prove2MeSourceProof.h_845c55972b82cdb43dfb6421 (X := fun s ω => gradient u s (y s ω) i)
    (fun t => (continuous_gradient hu t i).measurable.comp (hyad t))
    (fun ω t => ((continuous_gradient_uncurry hu i).tendsto (t, y t ω)).comp
      ((tendsto_id'.mpr nhdsWithin_le_nhds).prodMk_nhds (hyrc ω t)))
/-- The mixed diffusion integrand has finite energy on every bounded window, under a bound on
the gradient of the state function. -/
theorem lintegral_window_sq_mixedDiffusionIntegrand_lt_top (S : SdeData X) {c : ℝ}
    (hc : ∀ s x i, |gradient u s x i| ≤ c) (y : ℝ → Ω → Fin n → ℝ) (j : Fin d)
    (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖mixedDiffusionIntegrand u coeffs.σ s (y s ω) (X.X s ω) j‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤ :=
  lintegral_window_sq_le_of_abs_le (a := fun i ω s => coeffs.σ s (X.X s ω) i j) (c := c)
    (fun i => S.σ_meas i j) (fun _ω s => abs_mixedDiffusionIntegrand_le hc s _ _ j) T
    (fun i => S.σ_sq i j T hT)
/-- The mixed jump increment, read at an auxiliary path and at the solution, is jointly
measurable in the sample point, the time and the mark. -/
theorem measurable_mixedJumpIncrement (S : SdeData X)
    (hu : ContDiff ℝ 2 (Function.uncurry u)) (y : ℝ → Ω → Fin n → ℝ)
    (hy : Measurable (Function.uncurry y)) :
    Measurable fun p : Ω × ℝ × E =>
      mixedJumpIncrement u coeffs.γ p.2.1 (y p.2.1 p.1) (X.X p.2.1 p.1) p.2.2 := by
  have hyp : Measurable fun p : Ω × ℝ × E => y p.2.1 p.1 :=
    hy.comp (measurable_snd.fst.prodMk measurable_fst)
  have hγ : Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X.X p.2.1 p.1) p.2.2 :=
    measurable_pi_lambda _ fun i => S.γ_meas i
  change Measurable fun p : Ω × ℝ × E =>
    u p.2.1 (y p.2.1 p.1 + coeffs.γ p.2.1 (X.X p.2.1 p.1) p.2.2) - u p.2.1 (y p.2.1 p.1)
  exact (hu.continuous.measurable.comp (measurable_snd.fst.prodMk (hyp.add hγ))).sub
    (hu.continuous.measurable.comp (measurable_snd.fst.prodMk hyp))
/-- The mixed jump increment, read at a progressively measurable auxiliary path and at the
solution, is marked progressively measurable for the right-continuous filtration of the SDE
data. -/
theorem markedProgressivelyMeasurable_mixedJumpIncrement (S : SdeData X)
    (hu : ContDiff ℝ 2 (Function.uncurry u)) (y : ℝ → Ω → Fin n → ℝ)
    (hyp : ∀ i : Fin n,
      Probability.ProgressivelyMeasurable S.ℱ.rightCont fun ω s => y s ω i) :
    Probability.MarkedProgressivelyMeasurable S.ℱ.rightCont
      fun ω s e => mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e := by
  have hZ := _root_.Prove2MeSourceProof.h_c52cb68531741ca4a978b2b1 (ℱ := S.ℱ.rightCont)
    (coeffs := coeffs) (Xp := X.X) (Y := y) hyp
    (fun i => (S.γ_prog i).mono fun t => S.ℱ.le_rightCont t)
  have hg : Continuous fun q : ℝ × (Fin n → ℝ) × (Fin n → ℝ) =>
      u q.1 (q.2.1 + q.2.2) - u q.1 q.2.1 :=
    (hu.continuous.comp (continuous_fst.prodMk (continuous_snd.fst.add continuous_snd.snd))).sub
      (hu.continuous.comp (continuous_fst.prodMk continuous_snd.fst))
  have hg0 : (fun q : ℝ × (Fin n → ℝ) × (Fin n → ℝ) =>
      u q.1 (q.2.1 + q.2.2) - u q.1 q.2.1) 0 = 0 := by simp
  exact hg.comp_markedProgressivelyMeasurable hg0 hZ
/-- The mixed jump increment has finite energy on every bounded window, under a bound on the
gradient of the state function. -/
theorem lintegral_window_mark_sq_mixedJumpIncrement_lt_top (S : SdeData X)
    (hu : ContDiff ℝ 2 (Function.uncurry u)) {c : ℝ}
    (hc : ∀ s x i, |gradient u s x i| ≤ c) (hc0 : 0 ≤ c) (y : ℝ → Ω → Fin n → ℝ)
    (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e‖₊ : ℝ≥0∞) ^ 2
        ∂ν ∂volume ∂P < ⊤ :=
  _root_.Prove2MeSourceProof.h_7ac4f497a1ed78b320395909 (a := fun i ω s e => coeffs.γ s (X.X s ω) e i)
    (c := n * c) (fun i => S.γ_meas i)
    (fun _ω s e => abs_mixedJumpIncrement_le hu hc hc0 s _ _ e) T (fun i => S.γ_sq i T hT)
end Mixed

end LevyStochCalc.Ito.JumpFormula


