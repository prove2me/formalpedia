-- Prove2me | solution 1 for AppRunningTime.thmHalfPieces
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:12:41.297192+00:00
-- url     : https://prove2.me/submissions/c80e1510-0aed-4311-ad08-bbcab2dedf9e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppRunningTimeStatement
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_ClauseBound_Part_Bounds
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Series_Deriv
import Definitions.Def_GeneralPieces_GenF_Main
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Definitions.Def_GeneralPieces_Series_LemmaQ
import Definitions.Def_GeneralPieces_Ring_Bridge
import Definitions.Def_GeneralPieces_Ring_Dual
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_GeneralPieces_Ring_Pieces
import Definitions.Def_GeneralPieces_Ring_ThmHalfPieces
import Definitions.Def_GeneralPieces_DefGenPieces_ToPure
import Definitions.Def_GeneralPieces_DefGenPieces_MayAssume
import Definitions.Def_GeneralPieces_Group_Lemma
import Definitions.Def_GeneralPieces_Group_Calls
import Definitions.Def_GeneralPieces_ThmRunningTime
import Definitions.Def_GeneralPieces_Half_Main
import Definitions.Def_GeneralPieces_Tied_Bound
import Definitions.Def_GeneralPieces_Main
import Theorems.Thm_AppHalfPieces_pieceFacts
import Theorems.Thm_GeneralPieces_pieceFacts
import Theorems.Thm_GeneralPieces_thmHalfPieces


set_option autoImplicit false
section
section
open AppRunningTime
namespace AppRunningTime
theorem _root_.solution : ThmHalfPieces :=
  GeneralPieces.thmHalfPieces AppHalfPieces.pieceFacts
end AppRunningTime
