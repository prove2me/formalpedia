-- Prove2me | Definitions.Def_Tablet_curveRestrictTot
-- name    : Tablet_curveRestrictTot
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:48:19.945213+00:00
-- url     : https://prove2.me/theorems/c18b414d-e338-4f1a-9c15-4339044226ad
-- title:
--   curve Restrict Tot
-- statement:
--   Definitions and structural lemmas for curve Restrict Tot, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/curveRestrictTot.lean

import Definitions.Def_Tablet_curveRestrict
set_option autoImplicit false
noncomputable def curveRestrictTot {E : Type*} [MetricSpace E] (γ : Curve E) (a b : ℝ) :
    Curve E :=
-- BODY
  curveRestrict γ (min (max a 0) γ.len) (max (min (max a 0) γ.len) (min (max b 0) γ.len))
    (le_min (le_max_right _ _) γ.len_nonneg) (le_max_left _ _)
    (max_le (min_le_right _ _) (min_le_right _ _))


