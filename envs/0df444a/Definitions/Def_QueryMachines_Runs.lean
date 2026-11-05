-- Prove2me | Definitions.Def_QueryMachines_Runs
-- name    : QueryMachines_Runs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:46:39.543345+00:00
-- url     : https://prove2.me/theorems/e3fdf64a-12ea-42a4-b3f7-b75327454313
-- title:
--   Runs
-- statement:
--   Definitions and structural lemmas for Runs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Runs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_Kernel
import Definitions.Def_StepMachines_Prog_Stepped
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace QueryMachines.QueryMachine
open Groundwork
variable {Q A Q' A' C α β : Type}
section Subst
variable [HasSize C] {M : QueryMachine Q A α β} {N : QueryMachine Q' A' (C × Q) A} {O' : Q' → Option A'}
end Subst
end QueryMachines.QueryMachine
namespace QueryMachines
open Groundwork QueryMachine
end QueryMachines


