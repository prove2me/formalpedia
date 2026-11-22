-- Prove2me | Definitions.Def_LevyStochCalc_Ito_CutoffJumpTransfer_F000
-- name    : LevyStochCalc_Ito_CutoffJumpTransfer_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T10:03:31.544038+00:00
-- url     : https://prove2.me/theorems/54541206-3169-4811-b709-8eed47e516f5
-- title:
--   Source declarations: LevyStochCalc.Ito.CutoffJumpTransfer
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.CutoffJumpTransfer. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityStopping_F001
import Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityStopping_F002
import Definitions.Def_LevyStochCalc_Ito_CutoffPathAgreement_F000
import Definitions.Def_LevyStochCalc_Ito_CutoffPathAgreement_F001
import Definitions.Def_LevyStochCalc_Ito_JumpCoefficientPredictableZeroExt_F000
import Definitions.Def_LevyStochCalc_Ito_JumpCoefficientPredictableZeroExt_F001
import Definitions.Def_LevyStochCalc_Ito_JumpSideCompensator_F000
import Definitions.Def_LevyStochCalc_Ito_LeftLimIntegrandRegularity_F001
import Definitions.Def_LevyStochCalc_Ito_StabilityEstimate_F001
import Definitions.Def_LevyStochCalc_Ito_StabilityEstimate_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The jump side of the Itô–Lévy formula under the state cut-off

Along a path confined to a ball the state cut-off moves the jump increment and the
compensator-drift integrand by the same quantity, and that quantity vanishes at every atom of the
random measure. An integrand vanishing at the atoms has compensated integral minus its
compensator, so the two moves cancel: the *sum* of the compensated integral of the jump increment
and the compensator-drift integral is the same for a state function and for its cut-off, even
though neither term is.

## Main definitions

* `jumpIncrLeft` — the jump increment of a state function along a path, read at the left limits.

## Main statements

* `measurable_jumpIncrLeft`, `markedProgressivelyMeasurable_jumpIncrLeft`,
  `markedPredictable_zeroExtPos_jumpIncrLeft` — its admissibility and the predictability of its
  zero extension.
* `ae_jumpSide_cutoffFun₂_eq` — the jump side is unchanged by the cut-off on the event that the
  path stays in the ball.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.CutoffPath

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated
open LevyStochCalc.Ito.JumpFormula LevyStochCalc.Ito.JumpFormulaCutoff
open LevyStochCalc.Ito.JumpSplitting LevyStochCalc.Ito.JumpSide
open LevyStochCalc.Probability

universe u v

section Integrand

variable {Ω : Type u} {E : Type v} {n d : ℕ}

/-- The jump increment of a state function along a path, read at the left limits of the path. -/
noncomputable def jumpIncrLeft (w : ℝ → (Fin n → ℝ) → ℝ)
    (coeffs : Setting.JumpDiffusionCoeffs n d E) (Xp : ℝ → Ω → Fin n → ℝ)
    (ω : Ω) (s : ℝ) (e : E) : ℝ :=
  w s (leftLimPathAt Xp s ω + coeffs.γ s (leftLimPathAt Xp s ω) e)
    - w s (leftLimPathAt Xp s ω)
end Integrand

section Regularity

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {n d : ℕ}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {Xp : ℝ → Ω → Fin n → ℝ}
  {w : ℝ → (Fin n → ℝ) → ℝ}

/-- The state increment across a jump is jointly measurable in the time, the state and the
mark. -/
theorem measurable_stateIncr (hw : Continuous (Function.uncurry w))
    (hγ : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2) :
    Measurable fun q : ℝ × (Fin n → ℝ) × E =>
      w q.1 (q.2.1 + coeffs.γ q.1 q.2.1 q.2.2) - w q.1 q.2.1 := by
  have h1 : Measurable fun q : ℝ × (Fin n → ℝ) × E =>
      ((q.1, q.2.1 + coeffs.γ q.1 q.2.1 q.2.2) : ℝ × (Fin n → ℝ)) :=
    measurable_fst.prodMk (measurable_snd.fst.add hγ)
  have h2 : Measurable fun q : ℝ × (Fin n → ℝ) × E => ((q.1, q.2.1) : ℝ × (Fin n → ℝ)) :=
    measurable_fst.prodMk measurable_snd.fst
  exact (hw.measurable.comp h1).sub (hw.measurable.comp h2)
/-- The jump increment along the left limits of a jointly measurable path with left limits is
jointly measurable. -/
theorem measurable_jumpIncrLeft (hw : Continuous (Function.uncurry w))
    (hγ : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    (hXm : Measurable fun q : ℝ × Ω => Xp q.1 q.2)
    (hleft : ∀ (ω : Ω) (t : ℝ) (j : Fin n),
      ∃ L : ℝ, Tendsto (fun s => Xp s ω j) (𝓝[<] t) (𝓝 L)) :
    Measurable fun p : Ω × ℝ × E => jumpIncrLeft w coeffs Xp p.1 p.2.1 p.2.2 := by
  have hΛ : Measurable fun p : Ω × ℝ × E => leftLimPathAt Xp p.2.1 p.1 :=
    (measurable_uncurry_leftLimPathAt hXm hleft).comp
      (measurable_snd.fst.prodMk measurable_fst)
  exact (measurable_stateIncr hw hγ).comp
    (measurable_snd.fst.prodMk (hΛ.prodMk measurable_snd.snd))
/-- The jump increment along the left limits of an adapted path with left limits is marked
progressively measurable. -/
theorem markedProgressivelyMeasurable_jumpIncrLeft
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hw : Continuous (Function.uncurry w))
    (hγ : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t) (hXadapt : ∀ t : ℝ, Measurable[ℱ t] (Xp t))
    (hleft : ∀ (ω : Ω) (t : ℝ) (j : Fin n),
      ∃ L : ℝ, Tendsto (fun s => Xp s ω j) (𝓝[<] t) (𝓝 L)) :
    MarkedProgressivelyMeasurable ℱ (jumpIncrLeft w coeffs Xp) :=
  _root_.Prove2MeSourceProof.h_e745eea003d521dc58279648
    (fun j => progressivelyMeasurable_leftLimPathAt hℱ0 hXadapt hleft j)
    (F := fun s y e => w s (y + coeffs.γ s y e) - w s y) (measurable_stateIncr hw hγ)
variable {ν : Measure E} [SigmaFinite ν]

/-- The zero extension of the jump increment along the left limits of an adapted path with left
limits is marked predictable. -/
theorem markedPredictable_zeroExtPos_jumpIncrLeft
    (Xp : ℝ → Ω → Fin n → ℝ) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hw : Continuous (Function.uncurry w))
    (hγ : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    (hXadapt : ∀ t : ℝ, Measurable[ℱ t] (Xp t))
    (hleft : ∀ (ω : Ω) (t : ℝ) (j : Fin n),
      ∃ L : ℝ, Tendsto (fun s => Xp s ω j) (𝓝[<] t) (𝓝 L)) :
    MarkedPredictable ℱ ν (zeroExtPos (jumpIncrLeft w coeffs Xp)) :=
  _root_.Prove2MeSourceProof.h_5650dc54a894019ea9a2b291 Xp ℱ hXadapt
    (fun ω t _ j => hleft ω t j)
    (F := fun s y e => w s (y + coeffs.γ s y e) - w s y) (measurable_stateIncr hw hγ)
end Regularity

section Transfer

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}

end Transfer

end LevyStochCalc.Ito.CutoffPath


