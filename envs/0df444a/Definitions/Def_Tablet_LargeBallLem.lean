-- Prove2me | Definitions.Def_Tablet_LargeBallLem
-- name    : Tablet_LargeBallLem
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:09:58.95772+00:00
-- url     : https://prove2.me/theorems/491c63a5-b763-576a-b1e0-12b78146628b
-- title:
--   Large Ball Lem
-- statement:
--   Definitions and structural lemmas for Large Ball Lem, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/LargeBallLem.lean

import Definitions.Def_Tablet_DGammaBallMeasure
import Definitions.Def_Tablet_IsLSI
import Definitions.Def_Tablet_curveMeasure
import Definitions.Def_Tablet_CurveLipschitz
import Theorems.Thm_CurveLipschitz
import Theorems.Thm_DGammaBallMeasure

set_option autoImplicit false
open MeasureTheory Set ENNReal


