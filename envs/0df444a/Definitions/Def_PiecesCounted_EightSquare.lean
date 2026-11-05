-- Prove2me | Definitions.Def_PiecesCounted_EightSquare
-- name    : PiecesCounted_EightSquare
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T00:37:20.349541+00:00
-- url     : https://prove2.me/theorems/0aa8a25f-208c-441c-9065-688a9dcec249
-- title:
--   Eight Square
-- statement:
--   Definitions and structural lemmas for Eight Square, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/EightSquare.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCounted_Padded
import Definitions.Def_PiecesCounted_PaddedData
import Definitions.Def_PiecesCounted_Sizes
import Definitions.Def_PiecesFromEightSquares_LemPieces
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg
end PiecesCounted


