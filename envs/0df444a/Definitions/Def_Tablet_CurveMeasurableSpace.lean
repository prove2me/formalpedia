-- Prove2me | Definitions.Def_Tablet_CurveMeasurableSpace
-- name    : Tablet_CurveMeasurableSpace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:49:21.381452+00:00
-- url     : https://prove2.me/theorems/1ea284f8-3901-41cf-bbf4-0559749cf961
-- title:
--   Curve Measurable Space
-- statement:
--   Definitions and structural lemmas for Curve Measurable Space, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/CurveMeasurableSpace.lean

import Definitions.Def_Tablet_Curve
import Definitions.Def_Tablet_CurveLipschitz
import Definitions.Def_Tablet_curveRestrictTot
import Theorems.Thm_CurveLipschitz

set_option autoImplicit false
instance CurveMeasurableSpace {E : Type*} [MetricSpace E] [MeasurableSpace E] :
    MeasurableSpace (Curve E) :=
-- BODY
  MeasurableSpace.comap (fun γ => (γ.len, γ.toFun)) inferInstance


