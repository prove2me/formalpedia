-- Prove2me | Definitions.Def_Tablet_ApproximationMetric
-- name    : Tablet_ApproximationMetric
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:45:23.491271+00:00
-- url     : https://prove2.me/theorems/4c5f91e4-986b-5665-bee2-d5adb1f6b918
-- title:
--   Approximation Metric
-- statement:
--   Definitions and structural lemmas for Approximation Metric, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/ApproximationMetric.lean

import Definitions.Def_Tablet_MetricCurrent1
import Definitions.Def_Tablet_BoundaryZero
import Definitions.Def_Tablet_GeodesicPairing
import Definitions.Def_Tablet_MassSupFormula
import Definitions.Def_Tablet_PaoliniStepanovExists
import Definitions.Def_Tablet_BBAssertion
import Definitions.Def_Tablet_SurgeryEta
import Definitions.Def_Tablet_IsClosedCurve
import Definitions.Def_Tablet_IsPiecewiseGeodesic
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_curveMeasure
import Definitions.Def_Tablet_morreyNorm
import Theorems.Thm_BBAssertion
import Theorems.Thm_SurgeryEta

set_option autoImplicit false
open Set Filter Finset MeasureTheory ENNReal


