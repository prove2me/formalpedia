-- Prove2me | Definitions.Def_Tablet_RestrictCurrentFormula
-- name    : Tablet_RestrictCurrentFormula
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:50:56.72254+00:00
-- url     : https://prove2.me/theorems/335ed219-2289-4339-9353-737431400efc
-- title:
--   Restrict Current Formula
-- statement:
--   Definitions and structural lemmas for Restrict Current Formula, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/RestrictCurrentFormula.lean

import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_CurrentConcatAdditive
import Theorems.Thm_CurrentConcatAdditive

set_option autoImplicit false
open Set MeasureTheory


