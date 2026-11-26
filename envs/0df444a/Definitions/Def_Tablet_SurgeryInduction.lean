-- Prove2me | Definitions.Def_Tablet_SurgeryInduction
-- name    : Tablet_SurgeryInduction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:23:12.684492+00:00
-- url     : https://prove2.me/theorems/2c5e1cd5-5c4f-4765-9d89-9275a1b2d3f2
-- title:
--   Surgery Induction
-- statement:
--   Definitions and structural lemmas for Surgery Induction, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/SurgeryInduction.lean

import Definitions.Def_Tablet_GeodesicPairing
import Definitions.Def_Tablet_Curve
import Definitions.Def_Tablet_IsClosedCurve
import Definitions.Def_Tablet_IsPiecewiseGeodesic
import Definitions.Def_Tablet_IsDeltaEpsN
import Definitions.Def_Tablet_IsLSI
import Definitions.Def_Tablet_Form1
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_morreyNorm
import Definitions.Def_Tablet_curveMeasure
import Definitions.Def_Tablet_smallPieceCount
import Definitions.Def_Tablet_surgeryPotential
import Definitions.Def_Tablet_CutTypeI
import Definitions.Def_Tablet_CutTypeII
import Definitions.Def_Tablet_FullBallLem
import Definitions.Def_Tablet_SurgeryStepTypeI
import Definitions.Def_Tablet_SurgeryStepTypeII
import Theorems.Thm_CutTypeI
import Theorems.Thm_CutTypeII
import Theorems.Thm_FullBallLem
import Theorems.Thm_SurgeryStepTypeI
import Theorems.Thm_SurgeryStepTypeII

set_option autoImplicit false
open Set ENNReal


