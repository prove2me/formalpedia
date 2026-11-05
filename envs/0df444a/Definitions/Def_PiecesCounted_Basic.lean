-- Prove2me | Definitions.Def_PiecesCounted_Basic
-- name    : PiecesCounted_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T00:00:48.083125+00:00
-- url     : https://prove2.me/theorems/9a9e1a70-76dc-477c-88e4-8239f0401d43
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Basic.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCountedStatement
import Definitions.Def_GeneralPieces_DefGenPieces_ToPure
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg
end PiecesCounted


