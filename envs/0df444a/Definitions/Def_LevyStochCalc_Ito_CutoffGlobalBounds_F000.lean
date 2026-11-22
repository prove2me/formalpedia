-- Prove2me | Definitions.Def_LevyStochCalc_Ito_CutoffGlobalBounds_F000
-- name    : LevyStochCalc_Ito_CutoffGlobalBounds_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T09:02:37.654183+00:00
-- url     : https://prove2.me/theorems/f767fea3-a985-4c9c-ad7e-e72aadad7284
-- title:
--   Source declarations: LevyStochCalc.Ito.CutoffGlobalBounds
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.CutoffGlobalBounds. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaCutoffLocalise_F000
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaCutoffLocalise_F001
import Definitions.Def_LevyStochCalc_Ito_LocalDerivBounds_F000

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

/-- The cut-off vanishes outside the closed ball of radius `2R`. -/
theorem cutoffFun₂_eq_zero_of_lt {R : ℝ} (hR : 0 < R) {z : ℝ × (Fin n → ℝ)}
    (hz : 2 * R < ‖z‖) : cutoffFun₂ u R z.1 z.2 = 0 := by
  simp [cutoffFun₂, timeBoxCut_eq_zero hR hz]
/-- The time derivative of the cut-off vanishes outside the closed ball of radius `2R`. -/
theorem timeDeriv_cutoffFun₂_eq_zero {R : ℝ} (hR : 0 < R) {s : ℝ} {x : Fin n → ℝ}
    (h : 2 * R < ‖((s, x) : ℝ × (Fin n → ℝ))‖) : timeDeriv (cutoffFun₂ u R) s x = 0 := by
  have hopen : IsOpen {t : ℝ | 2 * R < ‖((t, x) : ℝ × (Fin n → ℝ))‖} :=
    isOpen_lt continuous_const (continuous_id.prodMk continuous_const).norm
  have hev : (fun t => cutoffFun₂ u R t x) =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
    filter_upwards [hopen.mem_nhds h] with t ht
    exact cutoffFun₂_eq_zero_of_lt hR (z := (t, x)) ht
  change deriv (fun t => cutoffFun₂ u R t x) s = 0
  rw [hev.deriv_eq]
  simp
/-- The gradient of the cut-off vanishes outside the closed ball of radius `2R`. -/
theorem gradient_cutoffFun₂_eq_zero {R : ℝ} (hR : 0 < R) {s : ℝ} {x : Fin n → ℝ}
    (h : 2 * R < ‖((s, x) : ℝ × (Fin n → ℝ))‖) (i : Fin n) :
    gradient (cutoffFun₂ u R) s x i = 0 := by
  have hopen : IsOpen {y : Fin n → ℝ | 2 * R < ‖((s, y) : ℝ × (Fin n → ℝ))‖} :=
    isOpen_lt continuous_const (continuous_const.prodMk continuous_id).norm
  have hev : cutoffFun₂ u R s =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [hopen.mem_nhds h] with y hy
    exact cutoffFun₂_eq_zero_of_lt hR (z := (s, y)) hy
  change fderiv ℝ (cutoffFun₂ u R s) x (Pi.single i 1) = 0
  rw [hev.fderiv_eq]
  simp
/-- The Hessian of the cut-off vanishes outside the closed ball of radius `2R`. -/
theorem hessian_cutoffFun₂_eq_zero {R : ℝ} (hR : 0 < R) {s : ℝ} {x : Fin n → ℝ}
    (h : 2 * R < ‖((s, x) : ℝ × (Fin n → ℝ))‖) (i j : Fin n) :
    hessian (cutoffFun₂ u R) s x i j = 0 := by
  have hopen : IsOpen {y : Fin n → ℝ | 2 * R < ‖((s, y) : ℝ × (Fin n → ℝ))‖} :=
    isOpen_lt continuous_const (continuous_const.prodMk continuous_id).norm
  have hev : (fun y => fderiv ℝ (cutoffFun₂ u R s) y (Pi.single i 1)) =ᶠ[𝓝 x]
      fun _ => (0 : ℝ) := by
    filter_upwards [hopen.mem_nhds h] with y hy
    exact gradient_cutoffFun₂_eq_zero hR hy i
  change fderiv ℝ (fun y => fderiv ℝ (cutoffFun₂ u R s) y (Pi.single i 1)) x (Pi.single j 1)
    = 0
  rw [hev.fderiv_eq]
  simp
end LevyStochCalc.Ito.JumpFormulaCutoff


