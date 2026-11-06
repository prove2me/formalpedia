-- Prove2me | Definitions.Def_Sat3Graph_Split
-- name    : Sat3Graph_Split
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:43:48.311497+00:00
-- url     : https://prove2.me/theorems/45174ac1-d50a-4459-a495-1064b41a1e7d
-- title:
--   Split
-- statement:
--   Definitions and structural lemmas for Split, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Split.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Sat3Graph_Defs
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_SizeCircuit_General
import Definitions.Def_GraphProblems_Engine
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace Sat3Graph
open Groundwork Groundwork.Prog CountKSat GraphProblems Eight.Width
end Sat3Graph


