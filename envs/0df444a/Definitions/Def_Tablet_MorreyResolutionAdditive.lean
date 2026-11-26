-- Prove2me | Definitions.Def_Tablet_MorreyResolutionAdditive
-- name    : Tablet_MorreyResolutionAdditive
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:07:39.837821+00:00
-- url     : https://prove2.me/theorems/5145bcb2-c555-47ce-b131-67496943d9e5
-- title:
--   Morrey Resolution Additive
-- statement:
--   Definitions and structural lemmas for Morrey Resolution Additive, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/MorreyResolutionAdditive.lean

import Definitions.Def_Tablet_curveMeasure
import Definitions.Def_Tablet_CurveLipschitz
import Definitions.Def_Tablet_IsGeodesicResolution
import Theorems.Thm_CurveLipschitz

set_option autoImplicit false
open MeasureTheory Set


