-- Prove2me | Definitions.Def_Tablet_curveWrapRestrict
-- name    : Tablet_curveWrapRestrict
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:00:57.783321+00:00
-- url     : https://prove2.me/theorems/31de98e0-f82d-4574-89b0-edf160e10de2
-- title:
--   curve Wrap Restrict
-- statement:
--   Definitions and structural lemmas for curve Wrap Restrict, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/curveWrapRestrict.lean

import Definitions.Def_Tablet_curveConcat
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_IsClosedCurve
set_option autoImplicit false
open Set
noncomputable def curveWrapRestrict {E : Type*} [MetricSpace E] (γ : Curve E) (t t' : ℝ)
    (hclosed : IsClosedCurve γ) (ht0 : 0 ≤ t) (htlen : t ≤ γ.len) (ht'0 : 0 ≤ t') (ht't : t' < t) :
    Curve E :=
-- BODY
  curveConcat (curveRestrict γ t γ.len ht0 htlen (le_refl _))
    (curveRestrict γ 0 t' (le_refl 0) ht'0 (by linarith))
    (by
      show γ.toFun (t + min (γ.len - t) (max 0 (γ.len - t)))
          = γ.toFun (0 + min (t' - 0) (max 0 0))
      have e1 : max (0:ℝ) (γ.len - t) = γ.len - t := max_eq_right (by linarith)
      have e2 : min (γ.len - t) (γ.len - t) = γ.len - t := min_self _
      have e3 : max (0:ℝ) (0:ℝ) = 0 := max_self 0
      have e4 : min (t' - 0) (0:ℝ) = 0 := by
        rw [sub_zero]; exact min_eq_right ht'0
      rw [e1, e2, e3, e4]
      have hz : t + (γ.len - t) = γ.len := by ring
      rw [hz, add_zero]
      exact hclosed)


