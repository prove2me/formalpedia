-- Prove2me | Definitions.Def_Tablet_SurgeryEta
-- name    : Tablet_SurgeryEta
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:41:08.839909+00:00
-- url     : https://prove2.me/theorems/446e6966-bf32-42c4-a18c-284b93c1161d
-- title:
--   Surgery Eta
-- statement:
--   Definitions and structural lemmas for Surgery Eta, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/SurgeryEta.lean

import Definitions.Def_Tablet_GeodesicPairing
import Definitions.Def_Tablet_Curve
import Definitions.Def_Tablet_IsClosedCurve
import Definitions.Def_Tablet_IsPiecewiseGeodesic
import Definitions.Def_Tablet_Form1
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_morreyNorm
import Definitions.Def_Tablet_curveMeasure
import Definitions.Def_Tablet_SurgeryLem
import Theorems.Thm_SurgeryLem

set_option autoImplicit false
open Set ENNReal


