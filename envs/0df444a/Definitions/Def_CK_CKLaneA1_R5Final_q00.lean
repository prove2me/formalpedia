-- Prove2me | Definitions.Def_CK_CKLaneA1_R5Final_q00
-- name    : CK_CKLaneA1_R5Final_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-08T05:49:44.68486+00:00
-- url     : https://prove2.me/theorems/cb473d01-2e4c-4c01-ad6d-d0d1ae632c06
-- title:
--   Courtade–Kumar proof module `CKLaneA1.R5Final (piece 1 of 5)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.R5Final (piece 1 of 5)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.R5Final (piece 1 of 5)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.R5Final (piece 1 of 5) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/R5Final (piece 1 of 5).lean)

import Definitions.Def_CK_CKLaneA1_R5Assembly
import Definitions.Def_CK_CKLaneA1_R5Data_C000
import Definitions.Def_CK_CKLaneA1_R5Data_C001
import Definitions.Def_CK_CKLaneA1_R5Data_C002
import Definitions.Def_CK_CKLaneA1_R5Data_C003
import Definitions.Def_CK_CKLaneA1_R5Data_C004
import Definitions.Def_CK_CKLaneA1_R5Data_C005
import Definitions.Def_CK_CKLaneA1_R5Data_C006
import Definitions.Def_CK_CKLaneA1_R5Data_C007
import Definitions.Def_CK_CKLaneA1_R5Data_C008
import Definitions.Def_CK_CKLaneA1_R5Data_C009__2
import Definitions.Def_CK_CKLaneA1_R5Data_C011__2
import Definitions.Def_CK_CKLaneA1_R5Data_C013
import Definitions.Def_CK_CKLaneA1_R5Data_C014
import Definitions.Def_CK_CKLaneA1_R5Data_C015
import Definitions.Def_CK_CKLaneA1_R5Data_C016
import Definitions.Def_CK_CKLaneA1_R5Data_C017



/-!
# CKLaneA1.R5Final — CE-stat row 5: `HighTCExclusion`

No retained stationary Case-E point has `t_C ≥ 1/100`: `highTC_of_cover` applied to the
kernel-checked cover `allStrips` (246 strips / 5514 cells, chunks `CKLaneA1.R5Data.C000–C017`).
-/

set_option autoImplicit false

namespace CKLaneA1.R5

open GeneralCK CKLaneP CKLaneN1.CEStat CKLaneA1.R5Data

/-- The full row-5 cover. -/
def allStrips : List Strip := strips000 ++ strips001 ++ strips002 ++ strips003 ++ strips004 ++ strips005 ++ strips006 ++ strips007 ++ strips008 ++ strips009 ++ strips010 ++ strips011 ++ strips012 ++ strips013 ++ strips014 ++ strips015 ++ strips016 ++ strips017

end CKLaneA1.R5


