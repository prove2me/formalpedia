-- Prove2me | Definitions.Def_Tablet_BasicCutClosed
-- name    : Tablet_BasicCutClosed
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:07:00.631985+00:00
-- url     : https://prove2.me/theorems/35120506-4a46-4e9f-a0f7-f3cf9537748d
-- title:
--   Basic Cut Closed
-- statement:
--   Definitions and structural lemmas for Basic Cut Closed, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/BasicCutClosed.lean

import Definitions.Def_Tablet_BasicCut
import Definitions.Def_Tablet_curveArc
import Definitions.Def_Tablet_ArcGeodesicResolution
import Definitions.Def_Tablet_BasicCutDiscardedResolutionGeneral
import Definitions.Def_Tablet_CurveConcatEndpoints
import Definitions.Def_Tablet_IsPiecewiseGeodesic
import Definitions.Def_Tablet_IsGeodesicResolution
import Definitions.Def_Tablet_IsGeodesicOn
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_curveWrapRestrict
import Definitions.Def_Tablet_curveConcat
import Definitions.Def_Tablet_GeodesicPairing
import Definitions.Def_Tablet_IsClosedCurve
import Theorems.Thm_ArcGeodesicResolution
import Theorems.Thm_BasicCutDiscardedResolutionGeneral
import Theorems.Thm_CurveConcatEndpoints

set_option autoImplicit false
open Set


