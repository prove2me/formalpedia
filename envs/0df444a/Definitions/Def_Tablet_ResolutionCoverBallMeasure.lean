-- Prove2me | Definitions.Def_Tablet_ResolutionCoverBallMeasure
-- name    : Tablet_ResolutionCoverBallMeasure
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:09:55.306844+00:00
-- url     : https://prove2.me/theorems/04b688b0-f761-5e89-9bf2-9321c12772ce
-- title:
--   Resolution Cover Ball Measure
-- statement:
--   Definitions and structural lemmas for Resolution Cover Ball Measure, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/ResolutionCoverBallMeasure.lean

import Definitions.Def_Tablet_IsGeodesicResolution
import Definitions.Def_Tablet_GeodesicMorreyLeTwo
import Definitions.Def_Tablet_curveMeasure
import Definitions.Def_Tablet_CurveLipschitz
import Definitions.Def_Tablet_morreyNorm
import Theorems.Thm_CurveLipschitz
import Theorems.Thm_GeodesicMorreyLeTwo

set_option autoImplicit false
open MeasureTheory Set ENNReal


