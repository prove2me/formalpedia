-- Prove2me | Definitions.Def_PiecesFromEightSquares_LemPieces
-- name    : PiecesFromEightSquares_LemPieces
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T00:33:30.804552+00:00
-- url     : https://prove2.me/theorems/87287746-910b-4b7e-8570-a794d6490931
-- title:
--   Lem Pieces
-- statement:
--   Definitions and structural lemmas for Lem Pieces, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesFromEightSquares/LemPieces.lean

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
set_option autoImplicit false
section
section
@[expose] section
namespace GeneralPieces
open Finset Groundwork PaddedDescent.F ClauseBound.Alg AppRunningTime Eight
end GeneralPieces
namespace AppRunningTime
open Eight GeneralPieces
end AppRunningTime


