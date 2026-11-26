-- Prove2me | Definitions.Def_Tablet_CutTypeII
-- name    : Tablet_CutTypeII
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:17:39.770803+00:00
-- url     : https://prove2.me/theorems/b044ea5c-b415-40cb-be6c-6a510bcf6f3e
-- title:
--   Cut Type II
-- statement:
--   Definitions and structural lemmas for Cut Type II, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/CutTypeII.lean

import Definitions.Def_Tablet_BasicCut
import Definitions.Def_Tablet_BasicCutClosed
import Definitions.Def_Tablet_BasicCutCurrent
import Definitions.Def_Tablet_BasicCutLength
import Definitions.Def_Tablet_BasicCutDiscardedResolution
import Definitions.Def_Tablet_BasicCutResolutionAtBreakpoints
import Definitions.Def_Tablet_DeltaEpsNFailureAtBreakpoints
import Definitions.Def_Tablet_C1SmallBall
import Definitions.Def_Tablet_curveMeasure
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_smallPieceCount
import Theorems.Thm_BasicCutClosed
import Theorems.Thm_BasicCutCurrent
import Theorems.Thm_BasicCutDiscardedResolution
import Theorems.Thm_BasicCutLength
import Theorems.Thm_BasicCutResolutionAtBreakpoints
import Theorems.Thm_C1SmallBall
import Theorems.Thm_DeltaEpsNFailureAtBreakpoints

set_option autoImplicit false
open Set ENNReal
set_option maxRecDepth 4000


