-- Prove2me | Definitions.Def_CountedRecursion_SolverRoom
-- name    : CountedRecursion_SolverRoom
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T09:03:15.857911+00:00
-- url     : https://prove2.me/theorems/3e06257b-a8ad-4b2b-983e-fd3c5ff15f50
-- title:
--   Solver Room
-- statement:
--   Definitions and structural lemmas for Solver Room, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverRoom.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverCall
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
end ExplicitCost


