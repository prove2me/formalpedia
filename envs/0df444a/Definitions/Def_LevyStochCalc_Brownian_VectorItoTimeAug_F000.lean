-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_VectorItoTimeAug_F000
-- name    : LevyStochCalc_Brownian_VectorItoTimeAug_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:36:34.267728+00:00
-- url     : https://prove2.me/theorems/9a1def61-90a4-4186-9c2f-b6b5afebd30b
-- title:
--   Source declarations: LevyStochCalc.Brownian.VectorItoTimeAug
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.VectorItoTimeAug. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_CoordDerivative_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoZero_F000
import Definitions.Def_LevyStochCalc_Brownian_VectorItoProcessVersion_F000

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

/-- The diffusion matrix with a time coordinate prepended: the time row is zero. -/
def timeAugDiffusion (H : Fin n → Fin d → Ω → ℝ → ℝ) : Fin (n + 1) → Fin d → Ω → ℝ → ℝ :=
  Fin.cons (fun _ _ _ => 0) H
/-- The drift with a time coordinate prepended: the time coordinate drifts at unit rate. -/
def timeAugDrift (bdrift : Fin n → Ω → ℝ → ℝ) : Fin (n + 1) → Ω → ℝ → ℝ :=
  Fin.cons (fun _ _ => 1) bdrift
/-- The initial value with a time coordinate prepended, starting at the origin. -/
def timeAugInit (X₀ : Ω → Fin n → ℝ) : Ω → Fin (n + 1) → ℝ := fun ω => Fin.cons 0 (X₀ ω)
/-- A process with its own time prepended as a coordinate. -/
def timeAugProcess (X : ℝ → Ω → Fin n → ℝ) : ℝ → Ω → Fin (n + 1) → ℝ :=
  fun t ω => Fin.cons t (X t ω)
variable (H : Fin n → Fin d → Ω → ℝ → ℝ)

theorem measurable_timeAugDiffusion (hHm : ∀ p k, Measurable (Function.uncurry (H p k)))
    (p : Fin (n + 1)) (k : Fin d) :
    Measurable (Function.uncurry (timeAugDiffusion H p k)) := by
  induction p using Fin.cases with
  | zero =>
    simp only [timeAugDiffusion, Fin.cons_zero]
    exact measurable_const
  | succ q => simpa [timeAugDiffusion] using hHm q k
theorem progressivelyMeasurable_timeAugDiffusion (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k)) (p : Fin (n + 1)) (k : Fin d) :
    Probability.ProgressivelyMeasurable ℱ (timeAugDiffusion H p k) := by
  induction p using Fin.cases with
  | zero =>
    simp only [timeAugDiffusion, Fin.cons_zero]
    exact Probability.progressivelyMeasurable_const (Ω := Ω) ℱ (0 : ℝ)
  | succ q => simpa [timeAugDiffusion] using hHp q k
theorem sq_timeAugDiffusion
    (hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (p : Fin (n + 1)) (k : Fin d) (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖timeAugDiffusion H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  induction p using Fin.cases with
  | zero => simp [timeAugDiffusion]
  | succ q => simpa [timeAugDiffusion] using hHs q k T hT
theorem measurable_timeAugDiffusion_add (hHm : ∀ p k, Measurable (Function.uncurry (H p k)))
    (p q : Fin (n + 1)) (k : Fin d) :
    Measurable (Function.uncurry fun ω s =>
      timeAugDiffusion H p k ω s + timeAugDiffusion H q k ω s) :=
  (measurable_timeAugDiffusion H hHm p k).add (measurable_timeAugDiffusion H hHm q k)
theorem progressivelyMeasurable_timeAugDiffusion_add (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k)) (p q : Fin (n + 1))
    (k : Fin d) :
    Probability.ProgressivelyMeasurable ℱ fun ω s =>
      timeAugDiffusion H p k ω s + timeAugDiffusion H q k ω s :=
  (progressivelyMeasurable_timeAugDiffusion H ℱ hHp p k).add
    (progressivelyMeasurable_timeAugDiffusion H ℱ hHp q k)
theorem sq_timeAugDiffusion_add
    (hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hqa : ∀ (p q : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s + H q k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (p q : Fin (n + 1)) (k : Fin d) (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖timeAugDiffusion H p k ω s + timeAugDiffusion H q k ω s‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤ := by
  induction p using Fin.cases with
  | zero =>
    induction q using Fin.cases with
    | zero => simp [timeAugDiffusion]
    | succ q' => simpa [timeAugDiffusion] using hHs q' k T hT
  | succ p' =>
    induction q using Fin.cases with
    | zero => simpa [timeAugDiffusion] using hHs p' k T hT
    | succ q' => simpa [timeAugDiffusion] using hqa p' q' k T hT
omit [MeasurableSpace Ω] in
theorem abs_timeAugDiffusion_le {C : ℝ} (hC0 : 0 ≤ C)
    (hCH : ∀ (p : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H p k ω s| ≤ C)
    (p : Fin (n + 1)) (k : Fin d) (ω : Ω) (s : ℝ) : |timeAugDiffusion H p k ω s| ≤ C := by
  induction p using Fin.cases with
  | zero => simpa [timeAugDiffusion] using hC0
  | succ q => simpa [timeAugDiffusion] using hCH q k ω s
variable (bdrift : Fin n → Ω → ℝ → ℝ)

theorem measurable_timeAugDrift (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    (p : Fin (n + 1)) : Measurable (Function.uncurry (timeAugDrift bdrift p)) := by
  induction p using Fin.cases with
  | zero =>
    simp only [timeAugDrift, Fin.cons_zero]
    exact measurable_const
  | succ q => simpa [timeAugDrift] using hbm q
theorem progressivelyMeasurable_timeAugDrift (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hbp : ∀ p, Probability.ProgressivelyMeasurable ℱ (bdrift p)) (p : Fin (n + 1)) :
    Probability.ProgressivelyMeasurable ℱ (timeAugDrift bdrift p) := by
  induction p using Fin.cases with
  | zero =>
    simp only [timeAugDrift, Fin.cons_zero]
    exact Probability.progressivelyMeasurable_const (Ω := Ω) ℱ (1 : ℝ)
  | succ q => simpa [timeAugDrift] using hbp q
omit [MeasurableSpace Ω] in
theorem abs_timeAugDrift_le {B : ℝ} (hB : ∀ (p : Fin n) (ω : Ω) (s : ℝ), |bdrift p ω s| ≤ B)
    (p : Fin (n + 1)) (ω : Ω) (s : ℝ) : |timeAugDrift bdrift p ω s| ≤ max B 1 := by
  induction p using Fin.cases with
  | zero => simp [timeAugDrift]
  | succ q => exact le_trans (by simpa [timeAugDrift] using hB q ω s) (le_max_left B 1)
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

end Weight

end LevyStochCalc.Brownian.Ito


