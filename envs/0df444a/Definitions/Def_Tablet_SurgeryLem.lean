-- Prove2me | Definitions.Def_Tablet_SurgeryLem
-- name    : Tablet_SurgeryLem
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:29:17.586035+00:00
-- url     : https://prove2.me/theorems/281af97f-fafd-4b5f-a48a-7afae0c0182a
-- title:
--   Surgery Lem
-- statement:
--   Definitions and structural lemmas for Surgery Lem, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/SurgeryLem.lean

import Definitions.Def_Tablet_GeodesicPairing
import Definitions.Def_Tablet_Curve
import Definitions.Def_Tablet_IsClosedCurve
import Definitions.Def_Tablet_IsPiecewiseGeodesic
import Definitions.Def_Tablet_Form1
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_morreyNorm
import Definitions.Def_Tablet_curveMeasure
import Definitions.Def_Tablet_surgeryPotential
import Definitions.Def_Tablet_smallPieceCount
import Definitions.Def_Tablet_InitialDeltaExists
import Definitions.Def_Tablet_SurgeryInduction
import Theorems.Thm_InitialDeltaExists
import Theorems.Thm_SurgeryInduction

set_option autoImplicit false
open Set ENNReal


