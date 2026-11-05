-- Prove2me | Definitions.Def_CountedRecursion_PolyQueries
-- name    : CountedRecursion_PolyQueries
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T05:56:33.987505+00:00
-- url     : https://prove2.me/theorems/9809fe14-5004-4d47-9d1c-b5b8ff136998
-- title:
--   Poly Queries
-- statement:
--   Definitions and structural lemmas for Poly Queries, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyQueries.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PolyLists
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace ExplicitCost
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.CertGridG Eight Eight.SecNetworks QueryMachines Printed
variable {α : Type} [Enc α]
section Parts
variable {p : α → Parent} (hp : PolyT p)
include hp
end Parts
section Net
variable {p : α → Parent} (hp : PolyT p)
include hp
end Net
end ExplicitCost


