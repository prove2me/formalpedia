-- Prove2me | solution 1 for AppHalfPieces.pieceFacts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:29:25.772116+00:00
-- url     : https://prove2.me/submissions/2a9d3f86-6c71-4447-addf-367039651e38

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
import Theorems.Thm_AppHalfPieces_opFacts
import Theorems.Thm_AppHalfPieces_o1
import Theorems.Thm_AppHalfPieces_lemmaQ
import Theorems.Thm_AppHalfPieces_lemmaDual
import Theorems.Thm_AppHalfPieces_zDvd
import Theorems.Thm_GeneralPieces_Dual_lemmaDual
import Theorems.Thm_GeneralPieces_Dual_zDvd
import Theorems.Thm_GeneralPieces_lemmaQ
import Theorems.Thm_GeneralPieces_o1
import Theorems.Thm_GeneralPieces_opFacts
import Theorems.Thm_GeneralPieces_pieceFacts


set_option autoImplicit false
section
section
open AppHalfPieces
namespace AppHalfPieces
theorem _root_.solution : PieceFacts :=
  GeneralPieces.pieceFacts lemmaQ lemmaDual opFacts o1 zDvd
end AppHalfPieces
