-- Prove2me | Definitions.Def_Tablet_BasicCutDiscardedResolution
-- name    : Tablet_BasicCutDiscardedResolution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:11:53.267906+00:00
-- url     : https://prove2.me/theorems/eb989a80-6c66-4fb1-a9e2-18568f383c95
-- title:
--   Basic Cut Discarded Resolution
-- statement:
--   Definitions and structural lemmas for Basic Cut Discarded Resolution, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/BasicCutDiscardedResolution.lean

import Definitions.Def_Tablet_BasicCut
import Definitions.Def_Tablet_IsPiecewiseGeodesicWith
import Definitions.Def_Tablet_RestrictPiecewiseGeodesic
import Definitions.Def_Tablet_ConcatGeodesicResolution
import Definitions.Def_Tablet_GeodesicIsPiecewiseGeodesic
import Definitions.Def_Tablet_CurveConcatEndpoints
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_curveWrapRestrict
import Theorems.Thm_ConcatGeodesicResolution
import Theorems.Thm_CurveConcatEndpoints
import Theorems.Thm_GeodesicIsPiecewiseGeodesic
import Theorems.Thm_RestrictPiecewiseGeodesic

set_option autoImplicit false
open Set


