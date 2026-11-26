-- Prove2me | Definitions.Def_Tablet_curveCurrent
-- name    : Tablet_curveCurrent
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:47:46.420317+00:00
-- url     : https://prove2.me/theorems/e1cf1a13-5da0-5009-b24f-b20a050ebeb5
-- title:
--   curve Current
-- statement:
--   Definitions and structural lemmas for curve Current, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/curveCurrent.lean

import Definitions.Def_Tablet_Curve
import Definitions.Def_Tablet_Form1
set_option autoImplicit false
noncomputable def curveCurrent {E : Type*} [MetricSpace E] (γ : Curve E) (ω : Form1 E) : ℝ :=
-- BODY
  ∫ t in (0:ℝ)..γ.len, ω.f (γ.toFun t) * deriv (ω.pi ∘ γ.toFun) t


