-- Prove2me | Definitions.Def_Tablet_SLLNCurves
-- name    : Tablet_SLLNCurves
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:57:35.436001+00:00
-- url     : https://prove2.me/theorems/2c8965c4-640a-54ea-9a76-7c9453a85dcf
-- title:
--   SLLNCurves
-- statement:
--   Definitions and structural lemmas for SLLNCurves, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/SLLNCurves.lean

import Definitions.Def_Tablet_SamplingRealizesAverages
import Definitions.Def_Tablet_PSFamily
import Definitions.Def_Tablet_CurveLenMeasurable
import Definitions.Def_Tablet_CurveCurrentMeasurable
import Definitions.Def_Tablet_CurveCurrentBound
import Definitions.Def_Tablet_ThetaL
import Theorems.Thm_CurveCurrentBound
import Theorems.Thm_CurveCurrentMeasurable
import Theorems.Thm_CurveLenMeasurable
import Theorems.Thm_SamplingRealizesAverages

set_option autoImplicit false
open MeasureTheory Filter Finset ENNReal


