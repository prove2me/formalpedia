-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_VectorItoTimeAug_F001
-- name    : LevyStochCalc_Brownian_VectorItoTimeAug_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:40:10.668804+00:00
-- url     : https://prove2.me/theorems/80707685-5558-47be-b960-df4653a9a928
-- title:
--   Source declarations: LevyStochCalc.Brownian.VectorItoTimeAug
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.VectorItoTimeAug. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_VectorItoTimeAug_F000

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

end Version

section Weight

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}
  (f' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] ℝ) (X : ℝ → Ω → Fin n → ℝ)
  (H : Fin n → Fin d → Ω → ℝ → ℝ)

theorem measurable_timeAugWeight
    (hmg : ∀ (q : Fin n) (k : Fin d), Measurable (Function.uncurry fun ω s =>
      coordDeriv f' q.succ (timeAugProcess X s ω) * H q k ω s))
    (p : Fin (n + 1)) (k : Fin d) :
    Measurable (Function.uncurry fun ω s =>
      coordDeriv f' p (timeAugProcess X s ω) * timeAugDiffusion H p k ω s) := by
  induction p using Fin.cases with
  | zero =>
    simp only [timeAugDiffusion, Fin.cons_zero, mul_zero]
    exact measurable_const
  | succ q => simpa [timeAugDiffusion] using hmg q k
theorem progressivelyMeasurable_timeAugWeight (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hpg : ∀ (q : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ
      fun ω s => coordDeriv f' q.succ (timeAugProcess X s ω) * H q k ω s)
    (p : Fin (n + 1)) (k : Fin d) :
    Probability.ProgressivelyMeasurable ℱ fun ω s =>
      coordDeriv f' p (timeAugProcess X s ω) * timeAugDiffusion H p k ω s := by
  induction p using Fin.cases with
  | zero =>
    simp only [timeAugDiffusion, Fin.cons_zero, mul_zero]
    exact Probability.progressivelyMeasurable_const ℱ (0 : ℝ)
  | succ q => simpa [timeAugDiffusion] using hpg q k
theorem sq_timeAugWeight
    (hqg : ∀ (q : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coordDeriv f' q.succ (timeAugProcess X s ω) * H q k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (p : Fin (n + 1)) (k : Fin d) (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coordDeriv f' p (timeAugProcess X s ω) * timeAugDiffusion H p k ω s‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤ := by
  induction p using Fin.cases with
  | zero => simp [timeAugDiffusion]
  | succ q => simpa [timeAugDiffusion] using hqg q k T hT
end Weight

end LevyStochCalc.Brownian.Ito


