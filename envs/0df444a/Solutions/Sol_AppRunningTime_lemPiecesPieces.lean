-- Prove2me | solution 1 for AppRunningTime.lemPiecesPieces
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:27:35.040601+00:00
-- url     : https://prove2.me/submissions/fdd707ba-c6a1-4acb-8f84-3fdff75cf20c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesFromEightSquaresStatement
import Definitions.Def_GeneralPieces_ThmRunningTime
import Definitions.Def_ClauseBoundStatement
import Definitions.Def_Eight_SecCrossing_LemPieces
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_Eight_App_Pieces
import Definitions.Def_Eight_App_Rate
import Definitions.Def_PiecesFromEightSquares_LemPieces
import Theorems.Thm_GeneralPieces_eight_isPieces
import Theorems.Thm_Eight_c_sum
import Theorems.Thm_Eight_lemPieces


set_option autoImplicit false
section
section
open AppRunningTime
open Eight GeneralPieces
namespace AppRunningTime
theorem _root_.solution : LemPiecesPieces := fun c hc =>
  ⟨eight_isPieces hc, fun lam hl => ⟨rfl, rfl, fun i hi => ⟨rfl, rfl, by
    have h1 := lemPieces.c_sum lam i hl hi
    unfold rho at h1
    linarith⟩⟩⟩
end AppRunningTime
