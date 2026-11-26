-- Prove2me | Definitions.Def_Tablet_ArcGeodesicResolution
-- name    : Tablet_ArcGeodesicResolution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:03:23.958582+00:00
-- url     : https://prove2.me/theorems/fe8c6cad-87f5-542d-85b8-3eb6d3dddfcc
-- title:
--   Arc Geodesic Resolution
-- statement:
--   Definitions and structural lemmas for Arc Geodesic Resolution, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/ArcGeodesicResolution.lean

import Definitions.Def_Tablet_curveArc
import Definitions.Def_Tablet_IsGeodesicResolution
import Definitions.Def_Tablet_RestrictGeodesicResolutionTruncated
import Definitions.Def_Tablet_ConcatGeodesicResolution
import Theorems.Thm_ConcatGeodesicResolution
import Theorems.Thm_RestrictGeodesicResolutionTruncated

set_option autoImplicit false
open Set


