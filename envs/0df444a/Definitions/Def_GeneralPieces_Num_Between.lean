-- Prove2me | Definitions.Def_GeneralPieces_Num_Between
-- name    : GeneralPieces_Num_Between
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T21:10:39.56878+00:00
-- url     : https://prove2.me/theorems/4969148b-f10c-495f-b57e-eba1bc1340f0
-- title:
--   Between
-- statement:
--   Definitions and structural lemmas for Between, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/Between.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_Asymptotic
import Definitions.Def_PaddedDescent_F_FuelCert
set_option autoImplicit false
section
section
@[expose] section
namespace GeneralPieces.Between
open Groundwork PaddedDescent.F Levels.Gen
def num (l : ℕ) : ℕ := 5 + 2 * (l - 2 * (l / 2))
def den (l : ℕ) : ℕ := 5 * 2 ^ ((l + 1) / 2)
end GeneralPieces.Between


