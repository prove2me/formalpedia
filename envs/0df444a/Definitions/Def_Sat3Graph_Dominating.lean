-- Prove2me | Definitions.Def_Sat3Graph_Dominating
-- name    : Sat3Graph_Dominating
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:54:48.698197+00:00
-- url     : https://prove2.me/theorems/4cafef53-aeab-4dd4-bcc6-1fbb60abb1ba
-- title:
--   Dominating
-- statement:
--   Definitions and structural lemmas for Dominating, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Dominating.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Sat3Graph_Defs
import Definitions.Def_Sat3Graph_Ask
import Definitions.Def_SplitSat_Sizes
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Read
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace Sat3Graph
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat GraphProblems Paper SizeCircuit SplitSat
end Sat3Graph


