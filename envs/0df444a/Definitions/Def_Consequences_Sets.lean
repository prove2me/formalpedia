-- Prove2me | Definitions.Def_Consequences_Sets
-- name    : Consequences_Sets
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T09:04:01.207737+00:00
-- url     : https://prove2.me/theorems/8921713e-add6-4f67-b2c9-d7a48de18a38
-- title:
--   Sets
-- statement:
--   Definitions and structural lemmas for Sets, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Consequences/Sets.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Consequences_Defs
import Definitions.Def_SplitCount_Main
import Definitions.Def_SizeCircuit_Main
import Definitions.Def_Complement_Readers
import Definitions.Def_Eight_ViaGrouping_CorGraph
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Cert
import Definitions.Def_GraphProblems_SetTM
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
set_option autoImplicit false
section
section
@[expose] section
namespace Consequences
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight Eight.ViaGrouping SplitCount SizeCircuit Complement
end Consequences


