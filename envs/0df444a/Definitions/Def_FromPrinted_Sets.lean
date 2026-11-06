-- Prove2me | Definitions.Def_FromPrinted_Sets
-- name    : FromPrinted_Sets
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T09:13:57.649751+00:00
-- url     : https://prove2.me/theorems/26723ad4-ac35-4677-ba52-f52c88179d96
-- title:
--   Sets
-- statement:
--   Definitions and structural lemmas for Sets, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Sets.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FromPrinted_GraphDefs
import Definitions.Def_FromPrinted_Count
import Definitions.Def_Consequences_Sets
import Definitions.Def_SizeCircuit_Main
import Definitions.Def_Complement_Readers
import Definitions.Def_Eight_ViaGrouping_CorGraph
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Cert
import Definitions.Def_GraphProblems_SetTM
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
open Consequences
namespace FromPrinted.Consequences
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight Eight.ViaGrouping FromPrinted.SplitCount SizeCircuit Complement
end FromPrinted.Consequences


