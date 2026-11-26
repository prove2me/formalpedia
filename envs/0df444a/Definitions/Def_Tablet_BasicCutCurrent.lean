-- Prove2me | Definitions.Def_Tablet_BasicCutCurrent
-- name    : Tablet_BasicCutCurrent
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:04:31.829682+00:00
-- url     : https://prove2.me/theorems/9bad3409-462f-5ccd-90e9-631ee64a5c03
-- title:
--   Basic Cut Current
-- statement:
--   Definitions and structural lemmas for Basic Cut Current, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/BasicCutCurrent.lean

import Definitions.Def_Tablet_BasicCut
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_CurrentConcatAdditive
import Definitions.Def_Tablet_CurrentReverse
import Definitions.Def_Tablet_CurrentResolutionAdditive
import Definitions.Def_Tablet_RestrictCurrentFormula
import Definitions.Def_Tablet_curveArc
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_curveWrapRestrict
import Definitions.Def_Tablet_GeodesicPairing
import Theorems.Thm_CurrentConcatAdditive
import Theorems.Thm_CurrentResolutionAdditive
import Theorems.Thm_CurrentReverse
import Theorems.Thm_RestrictCurrentFormula

set_option autoImplicit false
open Set


