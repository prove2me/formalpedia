-- Prove2me | Definitions.Def_PiecesCounted_Half
-- name    : PiecesCounted_Half
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T00:44:17.942915+00:00
-- url     : https://prove2.me/theorems/8135c66c-a9f3-406b-b356-3e0ad492278a
-- title:
--   Half
-- statement:
--   Definitions and structural lemmas for Half, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Half.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCountedStatement
import Definitions.Def_PiecesCounted_Padded
import Definitions.Def_PiecesCounted_PaddedData
import Definitions.Def_GeneralPieces_Main
import Definitions.Def_ToTuring_Lib_Int
import Definitions.Def_ToTuring_Lib_Unary
import Mathlib.Tactic
import Theorems.Thm_ClauseBound_Inst_Half_CertSmall_cnt

set_option autoImplicit false
section
section
@[expose] section
namespace PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg
@[expose] def halfShift (P : PiecesF) (lam : ℕ) : ℤ := -(((P.cnt 0 lam - 1) / 2 : ℕ) : ℤ)
end PiecesCounted


