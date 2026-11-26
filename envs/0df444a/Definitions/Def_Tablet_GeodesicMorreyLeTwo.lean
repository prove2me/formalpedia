-- Prove2me | Definitions.Def_Tablet_GeodesicMorreyLeTwo
-- name    : Tablet_GeodesicMorreyLeTwo
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:08:10.549702+00:00
-- url     : https://prove2.me/theorems/96f5ae17-cb6c-4ec7-833c-1a54890e7639
-- title:
--   Geodesic Morrey Le Two
-- statement:
--   Definitions and structural lemmas for Geodesic Morrey Le Two, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/GeodesicMorreyLeTwo.lean

import Definitions.Def_Tablet_curveMeasure
import Definitions.Def_Tablet_CurveLipschitz
import Definitions.Def_Tablet_morreyNorm
import Definitions.Def_Tablet_IsGeodesicOn
import Theorems.Thm_CurveLipschitz

set_option autoImplicit false
open MeasureTheory Set ENNReal


