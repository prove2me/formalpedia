-- Prove2me | Definitions.Def_Tablet_BasicCutDiscardedEval
-- name    : Tablet_BasicCutDiscardedEval
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:11:21.306644+00:00
-- url     : https://prove2.me/theorems/4158dbf6-b6b6-5c2c-9a55-3dae521fb0ca
-- title:
--   Basic Cut Discarded Eval
-- statement:
--   Definitions and structural lemmas for Basic Cut Discarded Eval, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/BasicCutDiscardedEval.lean

import Definitions.Def_Tablet_BasicCut
import Definitions.Def_Tablet_CurveConcatEndpoints
import Definitions.Def_Tablet_GeodesicPairing
import Definitions.Def_Tablet_IsClosedCurve
import Definitions.Def_Tablet_IsGeodesicOn
import Definitions.Def_Tablet_curveArc
import Definitions.Def_Tablet_curveConcat
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_curveWrapRestrict
import Theorems.Thm_CurveConcatEndpoints

set_option autoImplicit false
open Set


