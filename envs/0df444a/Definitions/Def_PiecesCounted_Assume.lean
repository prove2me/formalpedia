-- Prove2me | Definitions.Def_PiecesCounted_Assume
-- name    : PiecesCounted_Assume
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T00:07:47.820881+00:00
-- url     : https://prove2.me/theorems/eec095a8-6bf5-47a0-aa64-2cd11cd19877
-- title:
--   Assume
-- statement:
--   Definitions and structural lemmas for Assume, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Assume.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCounted_Trimmed
import Definitions.Def_PiecesCounted_PaddedData
import Definitions.Def_PiecesCounted_Sizes
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg
end PiecesCounted


