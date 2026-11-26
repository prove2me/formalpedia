-- Prove2me | Definitions.Def_Tablet_CurrentResolutionAdditive
-- name    : Tablet_CurrentResolutionAdditive
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:49:13.228898+00:00
-- url     : https://prove2.me/theorems/a2836831-c37e-555b-882f-11d8a7c0d14c
-- title:
--   Current Resolution Additive
-- statement:
--   Definitions and structural lemmas for Current Resolution Additive, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/CurrentResolutionAdditive.lean

import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_CurveLipschitz
import Definitions.Def_Tablet_IsGeodesicResolution
import Theorems.Thm_CurveLipschitz

set_option autoImplicit false
open MeasureTheory Set


