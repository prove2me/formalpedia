-- Prove2me | Definitions.Def_SourceProof_48bb348bd252ccd46dd07812
-- name    : SourceProof_48bb348bd252ccd46dd07812
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:38:29.920406+00:00
-- url     : https://prove2.me/theorems/afe12f72-2a6a-40c1-9bb9-272bebb29779
-- title:
--   LevyStochCalc source module: SourceProof_48bb348bd252ccd46dd07812
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.timeAug` comes from the `LevyStochCalc.Brownian.VectorItoTimeAug` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_VectorItoTimeAug_F000
import Definitions.Def_SourceProof_2631a3786acbcf68272d1d52

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Time as a state coordinate

Prepending a coordinate that drifts at unit rate and carries no diffusion turns a vector Itô
process `X` on `Fin n → ℝ` into one on `Fin (n + 1) → ℝ` whose path is `t ↦ (t, X_t)`. Itô's
formula for a time-dependent function of the state is then the state-only formula for the
augmented process.

## Main statements

* `LevyStochCalc.Brownian.Ito.timeAugDiffusion`, `timeAugDrift`, `timeAugInit`,
  `timeAugProcess` — the augmented data.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.timeAug` — the augmented path is a version of
  the augmented Itô process.
* `LevyStochCalc.Brownian.Ito.measurable_timeAugWeight` and its companions — the Itô formula's
  integrand hypotheses transfer to the augmented indices.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section Data

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}

variable (H : Fin n → Fin d → Ω → ℝ → ℝ)

variable (bdrift : Fin n → Ω → ℝ → ℝ)

end Data

section Version

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {W : Multidim.MultidimBrownianMotion P d}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ}
  {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
  {hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k)}
  {hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}


theorem _root_.Prove2MeSourceProof.h_48bb348bd252ccd46dd07812
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X) :
    IsVectorItoVersion W ℱ hcoord (timeAugDiffusion H)
      (measurable_timeAugDiffusion H hHm) (progressivelyMeasurable_timeAugDiffusion H ℱ hHp)
      (sq_timeAugDiffusion H hHs) (timeAugInit X₀) (timeAugDrift bdrift)
      (timeAugProcess X) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ω
    refine continuous_pi fun p => ?_
    induction p using Fin.cases with
    | zero =>
      simp only [LevyStochCalc.Brownian.Ito.timeAugProcess, Fin.cons_zero]
      exact continuous_id
    | succ q =>
      simp only [LevyStochCalc.Brownian.Ito.timeAugProcess, Fin.cons_succ]
      exact (continuous_apply q).comp (h.continuous_path ω)
  · intro t
    have hco : ∀ p : Fin (n + 1), Measurable[ℱ t] fun ω => LevyStochCalc.Brownian.Ito.timeAugProcess X t ω p := by
      intro p
      induction p using Fin.cases with
      | zero =>
        simp only [LevyStochCalc.Brownian.Ito.timeAugProcess, Fin.cons_zero]
        exact measurable_const
      | succ q =>
        simp only [LevyStochCalc.Brownian.Ito.timeAugProcess, Fin.cons_succ]
        exact (continuous_apply q).measurable.comp (h.adapted t).measurable
    refine Measurable.stronglyMeasurable ?_
    letI : MeasurableSpace Ω := ℱ t
    exact measurable_pi_lambda _ hco
  · intro t ht
    have hzero : ∀ᵐ ω ∂P, ∀ k : Fin d,
        LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord (LevyStochCalc.Brownian.Ito.timeAugDiffusion H) (LevyStochCalc.Brownian.Ito.measurable_timeAugDiffusion H hHm)
            (LevyStochCalc.Brownian.Ito.progressivelyMeasurable_timeAugDiffusion H ℱ hHp) (LevyStochCalc.Brownian.Ito.sq_timeAugDiffusion H hHs)
            0 k t ω = 0 := by
      refine MeasureTheory.ae_all_iff.mpr fun k => ?_
      have hz0 : LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (LevyStochCalc.Brownian.Ito.timeAugDiffusion H 0 k)
          (LevyStochCalc.Brownian.Ito.measurable_timeAugDiffusion H hHm 0 k)
          (LevyStochCalc.Brownian.Ito.progressivelyMeasurable_timeAugDiffusion H ℱ hHp 0 k)
          (LevyStochCalc.Brownian.Ito.sq_timeAugDiffusion H hHs 0 k) t =ᵐ[P] 0 :=
        _root_.Prove2MeSourceProof.h_2631a3786acbcf68272d1d52 (W.W k) ℱ (hcoord k) _ _ _ t
      filter_upwards [hz0] with ω hω
      simpa [LevyStochCalc.Brownian.Ito.coordItoIntegral] using hω
    have hone : ∫ _s in Set.Icc (0 : ℝ) t, (1 : ℝ) ∂volume = t := by
      rw [MeasureTheory.setIntegral_const]
      simp [MeasureTheory.measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal ht]
    filter_upwards [h.ae_eq t ht, hzero] with ω hX hz
    funext p
    induction p using Fin.cases with
    | zero =>
      simp only [LevyStochCalc.Brownian.Ito.timeAugProcess, Fin.cons_zero, LevyStochCalc.Brownian.Ito.vectorItoProcess, LevyStochCalc.Brownian.Ito.vectorItoMartingale,
        LevyStochCalc.Brownian.Ito.timeAugInit, LevyStochCalc.Brownian.Ito.timeAugDrift]
      rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => hz k, hone]
      simp
    | succ q =>
      simp only [LevyStochCalc.Brownian.Ito.timeAugProcess, Fin.cons_succ, LevyStochCalc.Brownian.Ito.vectorItoProcess, LevyStochCalc.Brownian.Ito.timeAugInit, LevyStochCalc.Brownian.Ito.timeAugDrift]
      exact congrFun hX q
end Version

section Weight

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}
  (f' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] ℝ) (X : ℝ → Ω → Fin n → ℝ)
  (H : Fin n → Fin d → Ω → ℝ → ℝ)

end Weight

end LevyStochCalc.Brownian.Ito


