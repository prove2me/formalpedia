-- Prove2me | Definitions.Def_GraphProblems_Sets
-- name    : GraphProblems_Sets
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T17:55:46.287456+00:00
-- url     : https://prove2.me/theorems/e749d08c-c739-4e58-bce7-6e0dbb4027bb
-- title:
--   Sets
-- statement:
--   Definitions and structural lemmas for Sets, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Sets.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_GraphProblems_Read
set_option autoImplicit false
section
section
@[expose] section
namespace GraphProblems
open Groundwork Groundwork.Prog CountKSat Finset
namespace Sets
variable {n : ℕ}
def trueSet (a : Fin n → Bool) : Finset (Fin n) := univ.filter fun i => a i = true
variable (G : SimpleGraph (Fin n)) (a : Fin n → Bool)
end Sets
open Sets
end GraphProblems


