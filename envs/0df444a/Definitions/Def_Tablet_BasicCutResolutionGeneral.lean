-- Prove2me | Definitions.Def_Tablet_BasicCutResolutionGeneral
-- name    : Tablet_BasicCutResolutionGeneral
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:07:25.206882+00:00
-- url     : https://prove2.me/theorems/a4c8b460-38e2-514d-a46c-6ee695a410c1
-- title:
--   Basic Cut Resolution General
-- statement:
--   Definitions and structural lemmas for Basic Cut Resolution General, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/BasicCutResolutionGeneral.lean

import Definitions.Def_Tablet_BasicCut
import Definitions.Def_Tablet_ArcGeodesicResolution
import Definitions.Def_Tablet_smallPieceCount
import Definitions.Def_Tablet_IsPiecewiseGeodesic
import Definitions.Def_Tablet_ConcatGeodesicResolution
import Definitions.Def_Tablet_GeodesicIsPiecewiseGeodesic
import Definitions.Def_Tablet_CurveConcatEndpoints
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_curveWrapRestrict
import Definitions.Def_Tablet_ShiftedBreakpointShortEdgeCount
import Definitions.Def_Tablet_SplicedBreakpointShortEdgeCount
import Theorems.Thm_ArcGeodesicResolution
import Theorems.Thm_ConcatGeodesicResolution
import Theorems.Thm_CurveConcatEndpoints
import Theorems.Thm_GeodesicIsPiecewiseGeodesic
import Theorems.Thm_ShiftedBreakpointShortEdgeCount
import Theorems.Thm_SplicedBreakpointShortEdgeCount

set_option autoImplicit false
open Set


