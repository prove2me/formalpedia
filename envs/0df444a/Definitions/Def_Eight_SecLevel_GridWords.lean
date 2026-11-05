-- Prove2me | Definitions.Def_Eight_SecLevel_GridWords
-- name    : Eight_SecLevel_GridWords
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:51:19.234388+00:00
-- url     : https://prove2.me/theorems/1c462e1d-56da-4932-a508-c6e466e5193f
-- title:
--   Sec Level Grid Words
-- statement:
--   Definitions and structural lemmas for Sec Level Grid Words, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_GridWords.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecLevel_Grid
import Definitions.Def_Eight_Level_Defs
import Mathlib.Tactic
import Theorems.Thm_Paper_mem_rectangles

set_option autoImplicit false
section
section
@[expose] section
namespace Eight.Level
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet
open Paper (Rectangle rectangles mem_rectangles FactorsThrough)
variable {g lam : ℕ}
end Eight.Level


