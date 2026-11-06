-- Prove2me | Definitions.Def_CountedRecursion_ProcedureCost
-- name    : CountedRecursion_ProcedureCost
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:42:05.757354+00:00
-- url     : https://prove2.me/theorems/385c348a-a919-451f-93d8-c1afab48b604
-- title:
--   Procedure Cost
-- statement:
--   Definitions and structural lemmas for Procedure Cost, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ProcedureCost.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CallFacts
import Definitions.Def_CountedRecursion_ParentSize
import Definitions.Def_CountedRecursion_Within
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
end ExplicitCost


