-- Prove2me | Definitions.Def_CountedRecursion_SolverStages
-- name    : CountedRecursion_SolverStages
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:40:55.04985+00:00
-- url     : https://prove2.me/theorems/0720243d-1cd7-42f5-ad8e-7fcd36c2fcf0
-- title:
--   Solver Stages
-- statement:
--   Definitions and structural lemmas for Solver Stages, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverStages.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverDefs
import Definitions.Def_CountedRecursion_Within
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace ExplicitCost
open Finset Groundwork QueryMachines Printed
variable {Q α : Type}
end ExplicitCost


