-- Prove2me | Definitions.Def_Sat3Graph_Sets
-- name    : Sat3Graph_Sets
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:55:05.072992+00:00
-- url     : https://prove2.me/theorems/3dbd146d-b0fc-4646-9fa3-258156b66690
-- title:
--   Sets
-- statement:
--   Definitions and structural lemmas for Sets, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Sets.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Sat3Graph_Defs
import Definitions.Def_Sat3Graph_Ask
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Read
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace Sat3Graph
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper SizeCircuit Complement SplitSat
end Sat3Graph


