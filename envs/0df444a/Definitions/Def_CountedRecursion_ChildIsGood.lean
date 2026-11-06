-- Prove2me | Definitions.Def_CountedRecursion_ChildIsGood
-- name    : CountedRecursion_ChildIsGood
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T06:34:38.701949+00:00
-- url     : https://prove2.me/theorems/6367fc28-b582-4f1b-826f-0d960d3d3916
-- title:
--   Child Is Good
-- statement:
--   Definitions and structural lemmas for Child Is Good, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ChildIsGood.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CallFacts
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
end ExplicitCost


