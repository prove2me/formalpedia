-- Prove2me | Definitions.Def_CK_CKLaneA1_FEFinal_q00_q00
-- name    : CK_CKLaneA1_FEFinal_q00_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T02:15:43.666991+00:00
-- url     : https://prove2.me/theorems/ca3bfa3b-c039-4d01-8e5d-48671aaade97
-- title:
--   Courtade–Kumar proof module `CKLaneA1.FEFinal (piece 1 of 4) (piece 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.FEFinal (piece 1 of 4) (piece 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.FEFinal (piece 1 of 4) (piece 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.FEFinal (piece 1 of 4) (piece 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/FEFinal (piece 1 of 4) (piece 1 of 3).lean)

import Definitions.Def_CK_CKLaneA1_FEStrip
import Definitions.Def_CK_CKLaneA1_Bridge
import Definitions.Def_CK_GeneralCK_CorrectionComplementCharts
import Definitions.Def_CK_CKLaneA1_FEData_C000
import Definitions.Def_CK_CKLaneA1_FEData_C001
import Definitions.Def_CK_CKLaneA1_FEData_C002
import Definitions.Def_CK_CKLaneA1_FEData_C003
import Definitions.Def_CK_CKLaneA1_FEData_C004
import Definitions.Def_CK_CKLaneA1_FEData_C005
import Definitions.Def_CK_CKLaneA1_FEData_C006
import Definitions.Def_CK_CKLaneA1_FEData_C007
import Definitions.Def_CK_CKLaneA1_FEData_C008
import Definitions.Def_CK_CKLaneA1_FEData_C009
import Definitions.Def_CK_CKLaneA1_FEData_C010
import Definitions.Def_CK_CKLaneA1_FEData_C011
import Definitions.Def_CK_CKLaneA1_FEData_C012
import Definitions.Def_CK_CKLaneA1_FEData_C013
import Definitions.Def_CK_CKLaneA1_FEData_C014
import Definitions.Def_CK_CKLaneA1_FEData_C015
import Definitions.Def_CK_CKLaneA1_FEData_C016



/-!
# CKLaneA1.FEFinal — `ChartOwners.fixedEdge`, closed

The generated cover (`17` chunk modules, each checked by `decide +kernel` on the Boolean
checker `stripOK`) plus the one-time soundness theorem `fe_pointwise_of_cover` give pointwise
positivity of `m11` and of the gap coefficient on `0 < u ≤ 1/50`, `1/40 ≤ w < 1/2`; the bridge
below converts it to the exact `ChartOwners.fixedEdge` field type.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace CKLaneA1

open GeneralCK GeneralCK.Correction GeneralCK.Correction.Natural GeneralCK.Correction.HighU

def feStrips : List FEStrip := FEData.strips000 ++ FEData.strips001 ++ FEData.strips002 ++ FEData.strips003 ++ FEData.strips004 ++ FEData.strips005 ++ FEData.strips006 ++ FEData.strips007 ++ FEData.strips008 ++ FEData.strips009 ++ FEData.strips010 ++ FEData.strips011 ++ FEData.strips012 ++ FEData.strips013 ++ FEData.strips014 ++ FEData.strips015 ++ FEData.strips016

end CKLaneA1


