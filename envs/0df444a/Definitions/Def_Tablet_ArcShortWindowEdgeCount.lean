-- Prove2me | Definitions.Def_Tablet_ArcShortWindowEdgeCount
-- name    : Tablet_ArcShortWindowEdgeCount
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:07:23.624097+00:00
-- url     : https://prove2.me/theorems/ace723f1-d94b-55ce-a3c6-4f33f23527c6
-- title:
--   Arc Short Window Edge Count
-- statement:
--   Definitions and structural lemmas for Arc Short Window Edge Count, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/ArcShortWindowEdgeCount.lean

import Definitions.Def_Tablet_curveArc
import Definitions.Def_Tablet_IsGeodesicResolution
import Definitions.Def_Tablet_ShortWindowAtMostOneLongEdge
import Definitions.Def_Tablet_ShiftedBreakpointShortEdgeCount
import Definitions.Def_Tablet_SplicedBreakpointShortEdgeCount
import Theorems.Thm_ShiftedBreakpointShortEdgeCount
import Theorems.Thm_ShortWindowAtMostOneLongEdge
import Theorems.Thm_SplicedBreakpointShortEdgeCount

set_option autoImplicit false
open Set


