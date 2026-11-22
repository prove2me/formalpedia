-- Prove2me | Definitions.Def_SourceProof_e4ab12abdaa00cc813656206
-- name    : SourceProof_e4ab12abdaa00cc813656206
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T12:45:28.78964+00:00
-- url     : https://prove2.me/theorems/c919b623-3a49-4bc8-b257-d83a265d9b01
-- title:
--   LevyStochCalc source module: SourceProof_e4ab12abdaa00cc813656206
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormulaCutoff.exists_globalBound_cutoffFun₂_c12` comes from the `LevyStochCalc.Ito.CutoffC12` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_CutoffGlobalBounds_F000
import Definitions.Def_LevyStochCalc_Ito_CutoffJumpTransfer_F000
import Definitions.Def_SourceProof_95728902748714b8e25fb455

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The time–space cut-off of a `C^{1,2}` state function

The time–space cut-off of radius `R` multiplies a state function by a jointly `C²` factor, so the
cut-off of a `C^{1,2}` function is again of class `C^{1,2}`. Its time derivative, gradient and
Hessian vanish outside the closed ball of radius `2R` and are continuous, hence are bounded
everywhere by one constant. Along a path confined to a ball the cut-off leaves the jump side of
the Itô–Lévy formula — the compensated integral of the jump increment plus the compensator-drift
integral — unchanged, and that transfer needs of the state function only the joint continuity of
the function and of its cut-off.

## Main statements

* `LevyStochCalc.Ito.JumpFormulaCutoff.exists_globalBound_cutoffFun₂_c12` — one constant bounds
  the time derivative, every gradient entry and every Hessian entry of the cut-off of a `C^{1,2}`
  function, at every time and every state.
* `LevyStochCalc.Ito.CutoffPath.ae_jumpSide_cutoffFun₂_eq_c12` — for a `C^{1,2}` state function
  the jump side is unchanged by the cut-off on the event that the path stays in the ball.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormulaCutoff

open LevyStochCalc.Ito.JumpFormula

variable {n : ℕ} {u : ℝ → (Fin n → ℝ) → ℝ}


theorem _root_.Prove2MeSourceProof.h_e4ab12abdaa00cc813656206 (hu : IsC12 u) {R : ℝ} (hR : 0 < R) :
    ∃ K : ℝ, 0 ≤ K ∧ (∀ s x, |timeDeriv (cutoffFun₂ u R) s x| ≤ K) ∧
      (∀ s x i, |gradient (cutoffFun₂ u R) s x i| ≤ K) ∧
      (∀ s x i j, |hessian (cutoffFun₂ u R) s x i j| ≤ K) := by
  obtain ⟨K, hK0, hKt, hKg, hKh⟩ :=
    _root_.Prove2MeSourceProof.h_95728902748714b8e25fb455 (LevyStochCalc.Ito.JumpFormula.isC12_cutoffFun₂ hu R) (-(2 * R)) (2 * R) (2 * R)
  refine ⟨K, hK0, fun s x => ?_, fun s x i => ?_, fun s x i j => ?_⟩
  · by_cases hz : 2 * R < ‖((s, x) : ℝ × (Fin n → ℝ))‖
    · rw [LevyStochCalc.Ito.JumpFormulaCutoff.timeDeriv_cutoffFun₂_eq_zero hR hz, abs_zero]
      exact hK0
    · have hz' : ‖((s, x) : ℝ × (Fin n → ℝ))‖ ≤ 2 * R := not_lt.mp hz
      simp only [Prod.norm_def, max_le_iff, Real.norm_eq_abs] at hz'
      exact hKt s x (abs_le.mp hz'.1) hz'.2
  · by_cases hz : 2 * R < ‖((s, x) : ℝ × (Fin n → ℝ))‖
    · rw [LevyStochCalc.Ito.JumpFormulaCutoff.gradient_cutoffFun₂_eq_zero hR hz i, abs_zero]
      exact hK0
    · have hz' : ‖((s, x) : ℝ × (Fin n → ℝ))‖ ≤ 2 * R := not_lt.mp hz
      simp only [Prod.norm_def, max_le_iff, Real.norm_eq_abs] at hz'
      exact hKg s x (abs_le.mp hz'.1) hz'.2 i
  · by_cases hz : 2 * R < ‖((s, x) : ℝ × (Fin n → ℝ))‖
    · rw [LevyStochCalc.Ito.JumpFormulaCutoff.hessian_cutoffFun₂_eq_zero hR hz i j, abs_zero]
      exact hK0
    · have hz' : ‖((s, x) : ℝ × (Fin n → ℝ))‖ ≤ 2 * R := not_lt.mp hz
      simp only [Prod.norm_def, max_le_iff, Real.norm_eq_abs] at hz'
      exact hKh s x (abs_le.mp hz'.1) hz'.2 i j
end LevyStochCalc.Ito.JumpFormulaCutoff

namespace LevyStochCalc.Ito.CutoffPath

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated
open LevyStochCalc.Ito.JumpFormula LevyStochCalc.Ito.JumpFormulaCutoff
open LevyStochCalc.Ito.JumpSplitting LevyStochCalc.Ito.JumpSide
open LevyStochCalc.Probability

universe u v

section Transfer

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}

end Transfer

end LevyStochCalc.Ito.CutoffPath


