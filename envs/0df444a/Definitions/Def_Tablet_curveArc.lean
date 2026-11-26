-- Prove2me | Definitions.Def_Tablet_curveArc
-- name    : Tablet_curveArc
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:01:48.851895+00:00
-- url     : https://prove2.me/theorems/e7b5da38-9e18-445d-88f2-605b16d26a30
-- title:
--   curve Arc
-- statement:
--   Definitions and structural lemmas for curve Arc, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/curveArc.lean

import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_curveWrapRestrict
import Definitions.Def_Tablet_IsClosedCurve
set_option autoImplicit false
open Set
noncomputable def curveArc {E : Type*} [MetricSpace E] (γ : Curve E) (hcl : IsClosedCurve γ)
    (t t' : ℝ) (ht0 : 0 ≤ t) (htl : t ≤ γ.len) (ht'0 : 0 ≤ t') (ht'l : t' ≤ γ.len) : Curve E :=
-- BODY
  if h : t ≤ t' then curveRestrict γ t t' ht0 h ht'l
  else curveWrapRestrict γ t t' hcl ht0 htl ht'0 (not_le.mp h)


