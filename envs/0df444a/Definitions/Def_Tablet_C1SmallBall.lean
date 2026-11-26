-- Prove2me | Definitions.Def_Tablet_C1SmallBall
-- name    : Tablet_C1SmallBall
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:09:53.104524+00:00
-- url     : https://prove2.me/theorems/ab22e90c-1369-533e-959e-117d5c6b4208
-- title:
--   C1 Small Ball
-- statement:
--   Definitions and structural lemmas for C1 Small Ball, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/C1SmallBall.lean

import Definitions.Def_Tablet_MorreySubadditive
import Definitions.Def_Tablet_MorreyResolutionAdditive
import Definitions.Def_Tablet_GeodesicMorreyLeTwo
import Definitions.Def_Tablet_IsPiecewiseGeodesicWith
import Theorems.Thm_GeodesicMorreyLeTwo
import Theorems.Thm_MorreyResolutionAdditive
import Theorems.Thm_MorreySubadditive

set_option autoImplicit false
open MeasureTheory Set ENNReal


