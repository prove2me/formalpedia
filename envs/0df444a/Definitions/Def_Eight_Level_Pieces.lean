-- Prove2me | Definitions.Def_Eight_Level_Pieces
-- name    : Eight_Level_Pieces
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:49:10.669868+00:00
-- url     : https://prove2.me/theorems/e78176d9-2ad7-48a1-8a9e-81d4f7f5cf30
-- title:
--   Pieces
-- statement:
--   Definitions and structural lemmas for Pieces, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Level/Pieces.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Level_Defs
import Definitions.Def_SingleBitPieces_Level_Pieces
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace Eight.Level
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Finset
end Eight.Level


