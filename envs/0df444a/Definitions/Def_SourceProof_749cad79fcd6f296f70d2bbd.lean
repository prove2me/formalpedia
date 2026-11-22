-- Prove2me | Definitions.Def_SourceProof_749cad79fcd6f296f70d2bbd
-- name    : SourceProof_749cad79fcd6f296f70d2bbd
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T09:07:23.160688+00:00
-- url     : https://prove2.me/theorems/26e764f2-f853-466f-bf4e-ac2406693d66
-- title:
--   LevyStochCalc source module: SourceProof_749cad79fcd6f296f70d2bbd
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormulaCutoff.exists_globalBound_cutoffFun₂` comes from the `LevyStochCalc.Ito.CutoffGlobalBounds` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_CutoffGlobalBounds_F000
import Definitions.Def_SourceProof_e7d37bbfbfbaa2bd6cca1c95

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Global bounds on the derivatives of a cut-off state function

A `C²` function of time and state multiplied by the time–space cut-off of radius `R` vanishes
outside the closed ball of radius `2R`, and so do its time derivative, gradient and Hessian: a
function vanishing on an open set has vanishing derivatives there. Each of the three is
continuous, so each is bounded on that closed ball, hence bounded everywhere by the same
constant.

## Main statements

* `timeDeriv_cutoffFun₂_eq_zero`, `gradient_cutoffFun₂_eq_zero`, `hessian_cutoffFun₂_eq_zero` —
  the derivatives of the cut-off vanish outside the closed ball of radius `2R`.
* `exists_globalBound_cutoffFun₂` — one constant bounds the time derivative, every gradient entry
  and every Hessian entry of the cut-off of a `C²` function, at every time and every state.
-/

open Filter Topology

namespace LevyStochCalc.Ito.JumpFormulaCutoff

open LevyStochCalc.Ito.JumpFormula

variable {n : ℕ} {u : ℝ → (Fin n → ℝ) → ℝ}


theorem _root_.Prove2MeSourceProof.h_749cad79fcd6f296f70d2bbd (hu : ContDiff ℝ 2 (Function.uncurry u)) {R : ℝ}
    (hR : 0 < R) :
    ∃ K : ℝ, 0 ≤ K ∧ (∀ s x, |timeDeriv (cutoffFun₂ u R) s x| ≤ K) ∧
      (∀ s x i, |gradient (cutoffFun₂ u R) s x i| ≤ K) ∧
      (∀ s x i j, |hessian (cutoffFun₂ u R) s x i j| ≤ K) := by
  obtain ⟨K, hK0, hKt, hKg, hKh⟩ :=
    _root_.Prove2MeSourceProof.h_e7d37bbfbfbaa2bd6cca1c95 (LevyStochCalc.Ito.JumpFormulaCutoff.contDiff_uncurry_cutoffFun₂ hu R) (-(2 * R)) (2 * R) (2 * R)
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


