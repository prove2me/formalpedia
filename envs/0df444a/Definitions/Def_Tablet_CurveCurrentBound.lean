-- Prove2me | Definitions.Def_Tablet_CurveCurrentBound
-- name    : Tablet_CurveCurrentBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:49:10.941135+00:00
-- url     : https://prove2.me/theorems/21ae9651-fdaa-510a-b0d0-149a03b08dbb
-- title:
--   Curve Current Bound
-- statement:
--   Definitions and structural lemmas for Curve Current Bound, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/CurveCurrentBound.lean

import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_CurveLipschitz
import Theorems.Thm_CurveLipschitz

set_option autoImplicit false
open scoped NNReal


