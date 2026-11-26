-- Prove2me | Definitions.Def_Tablet_BasicCutLength
-- name    : Tablet_BasicCutLength
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:05:13.889704+00:00
-- url     : https://prove2.me/theorems/5d64cf62-668f-49f6-8d1f-aca4bdb4ffdf
-- title:
--   Basic Cut Length
-- statement:
--   Definitions and structural lemmas for Basic Cut Length, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/BasicCutLength.lean

import Definitions.Def_Tablet_BasicCut
import Definitions.Def_Tablet_CurveLipschitz
import Definitions.Def_Tablet_curveConcat
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_curveWrapRestrict
import Theorems.Thm_CurveLipschitz

set_option autoImplicit false
open Set


