-- Prove2me | Definitions.Def_Tablet_ArcDeltaEpsNCount
-- name    : Tablet_ArcDeltaEpsNCount
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:08:35.535799+00:00
-- url     : https://prove2.me/theorems/15a7a850-76b4-5f21-85dd-e7a726610c77
-- title:
--   Arc Delta Eps NCount
-- statement:
--   Definitions and structural lemmas for Arc Delta Eps NCount, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/ArcDeltaEpsNCount.lean

import Definitions.Def_Tablet_curveArc
import Definitions.Def_Tablet_IsDeltaEpsN
import Definitions.Def_Tablet_ArcGeodesicResolution
import Definitions.Def_Tablet_RestrictPiecewiseGeodesic
import Definitions.Def_Tablet_ClampedLinearShortEdgeCount
import Definitions.Def_Tablet_ShiftedBreakpointShortEdgeCount
import Definitions.Def_Tablet_SplicedBreakpointShortEdgeCount
import Theorems.Thm_ArcGeodesicResolution
import Theorems.Thm_ClampedLinearShortEdgeCount
import Theorems.Thm_RestrictPiecewiseGeodesic
import Theorems.Thm_ShiftedBreakpointShortEdgeCount
import Theorems.Thm_SplicedBreakpointShortEdgeCount

set_option autoImplicit false
open Set


