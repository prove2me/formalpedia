-- Prove2me | Definitions.Def_Tablet_GeodesicSampledCurrent
-- name    : Tablet_GeodesicSampledCurrent
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:56:42.824732+00:00
-- url     : https://prove2.me/theorems/57373f1a-ae1b-574d-85fc-a865bddb96cc
-- title:
--   Geodesic Sampled Current
-- statement:
--   Definitions and structural lemmas for Geodesic Sampled Current, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/GeodesicSampledCurrent.lean

import Definitions.Def_Tablet_curveSampling
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_CurrentChordEstimate
import Definitions.Def_Tablet_CurrentConcatAdditive
import Definitions.Def_Tablet_CurrentResolutionAdditive
import Definitions.Def_Tablet_CurveLipschitz
import Definitions.Def_Tablet_RestrictCurrentFormula
import Definitions.Def_Tablet_curveRestrict
import Theorems.Thm_CurrentChordEstimate
import Theorems.Thm_CurrentConcatAdditive
import Theorems.Thm_CurrentResolutionAdditive
import Theorems.Thm_CurveLipschitz
import Theorems.Thm_RestrictCurrentFormula

set_option autoImplicit false


