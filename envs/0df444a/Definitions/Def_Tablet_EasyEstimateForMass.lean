-- Prove2me | Definitions.Def_Tablet_EasyEstimateForMass
-- name    : Tablet_EasyEstimateForMass
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:58:45.640987+00:00
-- url     : https://prove2.me/theorems/b7ccdc8e-86ab-4d60-8d43-539c47e1dc5c
-- title:
--   Easy Estimate For Mass
-- statement:
--   Definitions and structural lemmas for Easy Estimate For Mass, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/EasyEstimateForMass.lean

import Definitions.Def_Tablet_massOfFunctional
import Definitions.Def_Tablet_curveMeasure
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_CurveLipschitz
import Definitions.Def_Tablet_CurveCurrentBound
import Theorems.Thm_CurveCurrentBound
import Theorems.Thm_CurveLipschitz

set_option autoImplicit false
open MeasureTheory ENNReal


