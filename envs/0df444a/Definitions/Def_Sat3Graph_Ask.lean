-- Prove2me | Definitions.Def_Sat3Graph_Ask
-- name    : Sat3Graph_Ask
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:48:29.402524+00:00
-- url     : https://prove2.me/theorems/98e90925-8e3b-4c67-b003-6bc387f4bd56
-- title:
--   Ask
-- statement:
--   Definitions and structural lemmas for Ask, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Ask.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Sat3Graph_Defs
import Definitions.Def_Sat3Graph_Split
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_SizeCircuit_Gamma
import Definitions.Def_SizeCircuit_Sized
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace Sat3Graph
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight.Width SizeCircuit SplitSat
end Sat3Graph


