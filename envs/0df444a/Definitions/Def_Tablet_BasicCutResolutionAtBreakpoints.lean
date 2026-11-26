-- Prove2me | Definitions.Def_Tablet_BasicCutResolutionAtBreakpoints
-- name    : Tablet_BasicCutResolutionAtBreakpoints
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:14:34.86487+00:00
-- url     : https://prove2.me/theorems/7ecd592f-1e7d-5914-b3a9-fa23eaa5da2a
-- title:
--   Basic Cut Resolution At Breakpoints
-- statement:
--   Definitions and structural lemmas for Basic Cut Resolution At Breakpoints, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/BasicCutResolutionAtBreakpoints.lean

import Definitions.Def_Tablet_BasicCut
import Definitions.Def_Tablet_smallPieceCount
import Definitions.Def_Tablet_RestrictPiecewiseGeodesic
import Definitions.Def_Tablet_ConcatGeodesicResolution
import Definitions.Def_Tablet_GeodesicIsPiecewiseGeodesic
import Definitions.Def_Tablet_CurveConcatEndpoints
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_curveWrapRestrict
import Definitions.Def_Tablet_SubResolutionShortEdgeCount
import Definitions.Def_Tablet_ConcatResolutionShortEdgeCount
import Theorems.Thm_ConcatGeodesicResolution
import Theorems.Thm_ConcatResolutionShortEdgeCount
import Theorems.Thm_CurveConcatEndpoints
import Theorems.Thm_GeodesicIsPiecewiseGeodesic
import Theorems.Thm_RestrictPiecewiseGeodesic
import Theorems.Thm_SubResolutionShortEdgeCount

set_option autoImplicit false
open Set


