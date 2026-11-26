-- Prove2me | Definitions.Def_Tablet_BBAssertion
-- name    : Tablet_BBAssertion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:08:55.984394+00:00
-- url     : https://prove2.me/theorems/e288b0ec-efa7-5a7d-b506-db979abed01b
-- title:
--   BBAssertion
-- statement:
--   Definitions and structural lemmas for BBAssertion, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/BBAssertion.lean

import Definitions.Def_Tablet_MetricCurrent1
import Definitions.Def_Tablet_PSFamily
import Definitions.Def_Tablet_PaoliniStepanovExists
import Definitions.Def_Tablet_BoundaryZero
import Definitions.Def_Tablet_GeodesicPairing
import Definitions.Def_Tablet_BBSamplingDiagonal
import Definitions.Def_Tablet_DiagonalizationGeneral
import Definitions.Def_Tablet_ClosingUp
import Definitions.Def_Tablet_MassSupFormula
import Definitions.Def_Tablet_MassFamilyBound
import Definitions.Def_Tablet_MassPosOfNonzero
import Definitions.Def_Tablet_EasyEstimateForMass
import Definitions.Def_Tablet_IsClosedCurve
import Definitions.Def_Tablet_IsPiecewiseGeodesic
import Definitions.Def_Tablet_curveCurrent
import Theorems.Thm_BBSamplingDiagonal
import Theorems.Thm_ClosingUp
import Theorems.Thm_DiagonalizationGeneral
import Theorems.Thm_EasyEstimateForMass
import Theorems.Thm_MassFamilyBound
import Theorems.Thm_MassPosOfNonzero

set_option autoImplicit false
open Set Filter Finset MeasureTheory ENNReal


