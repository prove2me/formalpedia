-- Prove2me | Definitions.Def_Tablet_SamplingPiecewiseGeodesic
-- name    : Tablet_SamplingPiecewiseGeodesic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:58:21.105919+00:00
-- url     : https://prove2.me/theorems/1ab568b4-1807-4dd1-8088-ef82cd65cccb
-- title:
--   Sampling Piecewise Geodesic
-- statement:
--   Definitions and structural lemmas for Sampling Piecewise Geodesic, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/SamplingPiecewiseGeodesic.lean

import Definitions.Def_Tablet_curveSampling
import Definitions.Def_Tablet_IsPiecewiseGeodesic
import Definitions.Def_Tablet_GeodesicIsPiecewiseGeodesic
import Definitions.Def_Tablet_ConcatPiecewiseGeodesic
import Theorems.Thm_ConcatPiecewiseGeodesic
import Theorems.Thm_GeodesicIsPiecewiseGeodesic

set_option autoImplicit false
open Set


