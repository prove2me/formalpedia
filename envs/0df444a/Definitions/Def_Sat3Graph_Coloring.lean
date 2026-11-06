-- Prove2me | Definitions.Def_Sat3Graph_Coloring
-- name    : Sat3Graph_Coloring
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:50:42.313509+00:00
-- url     : https://prove2.me/theorems/8a5831e6-5725-4719-ad11-131191fd6030
-- title:
--   Coloring
-- statement:
--   Definitions and structural lemmas for Coloring, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Coloring.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Sat3Graph_Defs
import Definitions.Def_Sat3Graph_Split
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_GraphProblems_Color
import Definitions.Def_GraphProblems_Read
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace Sat3Graph
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight.Width SplitSat
end Sat3Graph


