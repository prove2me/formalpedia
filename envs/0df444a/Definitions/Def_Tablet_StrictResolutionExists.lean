-- Prove2me | Definitions.Def_Tablet_StrictResolutionExists
-- name    : Tablet_StrictResolutionExists
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:01:40.16255+00:00
-- url     : https://prove2.me/theorems/e16cfad6-a1f5-4ab3-a44f-07846386a34e
-- title:
--   Strict Resolution Exists
-- statement:
--   Definitions and structural lemmas for Strict Resolution Exists, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/StrictResolutionExists.lean

import Definitions.Def_Tablet_IsGeodesicResolution
import Definitions.Def_Tablet_IsPiecewiseGeodesic
import Definitions.Def_Tablet_MinimizingResolutionStrict
import Definitions.Def_Tablet_smallPieceCount
import Theorems.Thm_MinimizingResolutionStrict

set_option autoImplicit false
open Set


