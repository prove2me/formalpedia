-- Prove2me | Definitions.Def_Tablet_CurveEvalJointMeasurable
-- name    : Tablet_CurveEvalJointMeasurable
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:49:51.608353+00:00
-- url     : https://prove2.me/theorems/605fb2e8-9681-4aee-a624-467e6bfe142d
-- title:
--   Curve Eval Joint Measurable
-- statement:
--   Definitions and structural lemmas for Curve Eval Joint Measurable, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/CurveEvalJointMeasurable.lean

import Definitions.Def_Tablet_CurveMeasurableSpace
import Definitions.Def_Tablet_CurveLipschitz
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Theorems.Thm_CurveLipschitz

set_option autoImplicit false
open MeasureTheory


