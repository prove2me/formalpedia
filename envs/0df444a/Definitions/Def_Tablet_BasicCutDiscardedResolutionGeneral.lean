-- Prove2me | Definitions.Def_Tablet_BasicCutDiscardedResolutionGeneral
-- name    : Tablet_BasicCutDiscardedResolutionGeneral
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:03:59.592205+00:00
-- url     : https://prove2.me/theorems/a169d980-2ecd-5f75-8a23-96f8a0f2ce7a
-- title:
--   Basic Cut Discarded Resolution General
-- statement:
--   Definitions and structural lemmas for Basic Cut Discarded Resolution General, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/BasicCutDiscardedResolutionGeneral.lean

import Definitions.Def_Tablet_BasicCut
import Definitions.Def_Tablet_IsPiecewiseGeodesicWith
import Definitions.Def_Tablet_ConcatGeodesicResolution
import Definitions.Def_Tablet_GeodesicIsPiecewiseGeodesic
import Definitions.Def_Tablet_curveArc
import Definitions.Def_Tablet_curveConcat
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_curveWrapRestrict
import Theorems.Thm_ConcatGeodesicResolution
import Theorems.Thm_GeodesicIsPiecewiseGeodesic

set_option autoImplicit false
open Set


