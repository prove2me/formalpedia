-- Prove2me | Definitions.Def_Tablet_FullBallLem
-- name    : Tablet_FullBallLem
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:13:08.268535+00:00
-- url     : https://prove2.me/theorems/feb186ea-6503-44cb-82d7-eaf07fff5191
-- title:
--   Full Ball Lem
-- statement:
--   Definitions and structural lemmas for Full Ball Lem, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/FullBallLem.lean

import Definitions.Def_Tablet_LargeBallLem
import Definitions.Def_Tablet_DGammaBallMeasure
import Definitions.Def_Tablet_IsDeltaEpsN
import Definitions.Def_Tablet_C1SmallBall
import Definitions.Def_Tablet_morreyNorm
import Definitions.Def_Tablet_BigEdgeWindowPacking
import Definitions.Def_Tablet_StraddleAtMostOneEdge
import Definitions.Def_Tablet_ResolutionCoverBallMeasure
import Definitions.Def_Tablet_ArcLocalization
import Theorems.Thm_ArcLocalization
import Theorems.Thm_BigEdgeWindowPacking
import Theorems.Thm_C1SmallBall
import Theorems.Thm_DGammaBallMeasure
import Theorems.Thm_LargeBallLem
import Theorems.Thm_ResolutionCoverBallMeasure
import Theorems.Thm_StraddleAtMostOneEdge

set_option autoImplicit false
open MeasureTheory Set ENNReal


