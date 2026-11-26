-- Prove2me | Definitions.Def_Tablet_ClosingUp
-- name    : Tablet_ClosingUp
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:00:30.257528+00:00
-- url     : https://prove2.me/theorems/a76717be-3233-5af1-b625-023618eac983
-- title:
--   Closing Up
-- statement:
--   Definitions and structural lemmas for Closing Up, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/ClosingUp.lean

import Definitions.Def_Tablet_PSFamily
import Definitions.Def_Tablet_GeodesicPairing
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_curveSampling
import Definitions.Def_Tablet_curveConcat
import Definitions.Def_Tablet_SamplingEndpoints
import Definitions.Def_Tablet_CurveConcatEndpoints
import Definitions.Def_Tablet_SamplingPiecewiseGeodesic
import Definitions.Def_Tablet_GeodesicIsPiecewiseGeodesic
import Definitions.Def_Tablet_ConcatPiecewiseGeodesic
import Definitions.Def_Tablet_GeodesicSampledCurrent
import Definitions.Def_Tablet_CurveLipschitz
import Definitions.Def_Tablet_IsClosedCurve
import Definitions.Def_Tablet_IsPiecewiseGeodesicWith
import Definitions.Def_Tablet_CurrentConcatAdditive
import Definitions.Def_Tablet_CurrentReverse
import Definitions.Def_Tablet_CurveCurrentBound
import Theorems.Thm_ConcatPiecewiseGeodesic
import Theorems.Thm_CurrentConcatAdditive
import Theorems.Thm_CurrentReverse
import Theorems.Thm_CurveConcatEndpoints
import Theorems.Thm_CurveCurrentBound
import Theorems.Thm_CurveLipschitz
import Theorems.Thm_GeodesicIsPiecewiseGeodesic
import Theorems.Thm_GeodesicSampledCurrent
import Theorems.Thm_SamplingEndpoints
import Theorems.Thm_SamplingPiecewiseGeodesic

set_option autoImplicit false
open Set Filter Finset MeasureTheory


