-- Prove2me | Definitions.Def_FromPrinted_Dom
-- name    : FromPrinted_Dom
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T09:23:28.873045+00:00
-- url     : https://prove2.me/theorems/fe6bdfe6-3852-41c0-9567-79e49ca10132
-- title:
--   Dom
-- statement:
--   Definitions and structural lemmas for Dom, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Dom.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FromPrinted_GraphDefs
import Definitions.Def_FromPrinted_Sets
import Definitions.Def_Consequences_Dom
import Definitions.Def_SplitCount_Sizes
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Cert
import Definitions.Def_GraphProblems_DomTree
import Definitions.Def_CountKSat_Walk
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
open Consequences SplitCount
namespace FromPrinted.Consequences
open Groundwork Groundwork.Prog Groundwork.Stepped Groundwork.Sparsify CountKSat GraphProblems Paper
end FromPrinted.Consequences


