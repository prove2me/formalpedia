-- Prove2me | Definitions.Def_Tablet_CurrentConcatAdditive
-- name    : Tablet_CurrentConcatAdditive
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:49:17.342029+00:00
-- url     : https://prove2.me/theorems/fee952b3-a929-419f-acf8-55ecd90f4227
-- title:
--   Current Concat Additive
-- statement:
--   Definitions and structural lemmas for Current Concat Additive, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/CurrentConcatAdditive.lean

import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_curveConcat
import Definitions.Def_Tablet_CurveLipschitz
import Theorems.Thm_CurveLipschitz

set_option autoImplicit false
open Set MeasureTheory


