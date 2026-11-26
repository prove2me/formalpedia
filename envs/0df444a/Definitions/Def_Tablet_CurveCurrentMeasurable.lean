-- Prove2me | Definitions.Def_Tablet_CurveCurrentMeasurable
-- name    : Tablet_CurveCurrentMeasurable
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:54:34.059967+00:00
-- url     : https://prove2.me/theorems/fa31b5c1-db9f-448e-bff5-060c0f43a33a
-- title:
--   Curve Current Measurable
-- statement:
--   Definitions and structural lemmas for Curve Current Measurable, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/CurveCurrentMeasurable.lean

import Definitions.Def_Tablet_CurveScaledEvalMeasurable
import Definitions.Def_Tablet_CurveCurrentBound
import Definitions.Def_Tablet_CurrentChordEstimate
import Definitions.Def_Tablet_CurrentResolutionAdditive
import Definitions.Def_Tablet_RestrictCurrentFormula
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_Form1
import Theorems.Thm_CurrentChordEstimate
import Theorems.Thm_CurrentResolutionAdditive
import Theorems.Thm_CurveCurrentBound
import Theorems.Thm_CurveScaledEvalMeasurable
import Theorems.Thm_RestrictCurrentFormula

set_option autoImplicit false
open MeasureTheory Finset


