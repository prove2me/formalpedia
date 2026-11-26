-- Prove2me | Definitions.Def_Tablet_InitialDeltaExists
-- name    : Tablet_InitialDeltaExists
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:03:45.398544+00:00
-- url     : https://prove2.me/theorems/5d09ed16-6091-50ce-b6b7-e7122ace756f
-- title:
--   Initial Delta Exists
-- statement:
--   Definitions and structural lemmas for Initial Delta Exists, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/InitialDeltaExists.lean

import Definitions.Def_Tablet_StrictResolutionExists
import Definitions.Def_Tablet_smallPieceCount
import Definitions.Def_Tablet_IsDeltaEpsN
import Definitions.Def_Tablet_IsPiecewiseGeodesic
import Definitions.Def_Tablet_IsClosedCurve
import Theorems.Thm_StrictResolutionExists

set_option autoImplicit false
open Set


