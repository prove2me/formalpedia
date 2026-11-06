-- Prove2me | Definitions.Def_FromPrinted_Circuits
-- name    : FromPrinted_Circuits
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T09:31:59.150205+00:00
-- url     : https://prove2.me/theorems/00960c86-bd34-4230-96d1-c1d316e9a7ac
-- title:
--   Circuits
-- statement:
--   Definitions and structural lemmas for Circuits, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Circuits.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FromPrinted_GraphDefs
import Definitions.Def_FromPrinted_Count
import Definitions.Def_FromPrinted_Sets
import Definitions.Def_FromPrinted_Dom
import Definitions.Def_Consequences_Main
import Definitions.Def_Eight_ViaGrouping_CorGraph
import Definitions.Def_Eight_ViaGrouping_CorENP
import Definitions.Def_GraphProblems_Host
import Definitions.Def_GraphProblems_SetTM
import Definitions.Def_SplitCount_Sizes
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Color
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
open Consequences
namespace FromPrinted.Consequences
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight Eight.ViaGrouping FromPrinted.SplitCount Turing
end FromPrinted.Consequences


