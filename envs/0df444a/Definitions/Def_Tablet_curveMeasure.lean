-- Prove2me | Definitions.Def_Tablet_curveMeasure
-- name    : Tablet_curveMeasure
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:58:17.952813+00:00
-- url     : https://prove2.me/theorems/4cc2b6d4-93d7-4788-ad09-09fbe070d0bc
-- title:
--   curve Measure
-- statement:
--   Definitions and structural lemmas for curve Measure, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/curveMeasure.lean

import Definitions.Def_Tablet_Curve
set_option autoImplicit false
open MeasureTheory Set
noncomputable def curveMeasure {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (γ : Curve E) : Measure E :=
-- BODY
  Measure.map γ.toFun (volume.restrict (Set.Icc 0 γ.len))


