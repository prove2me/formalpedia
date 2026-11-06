-- Prove2me | Definitions.Def_Eight_ViaGrouping_CorGraph
-- name    : Eight_ViaGrouping_CorGraph
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:23:55.908018+00:00
-- url     : https://prove2.me/theorems/e9110e4b-3d4f-439e-9841-fbae7d6ee785
-- title:
--   Cor Graph
-- statement:
--   Definitions and structural lemmas for Cor Graph, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/CorGraph.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_Graph
import Definitions.Def_Eight_ViaGrouping_CorDefs2
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Color
import Definitions.Def_GraphProblems_Blocks
import Definitions.Def_GraphProblems_DomTree
import Definitions.Def_GraphProblems_Cert
import Definitions.Def_GraphProblems_SetTM
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_GraphProblems_Host
import Definitions.Def_CountKSat_Walk
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Stepped Paper CountKSat GraphProblems Finset Turing
variable {En : ℕ → ℕ → ℕ → StepMachine (List Unit × Fml) (List Bool)}
end Eight.ViaGrouping


