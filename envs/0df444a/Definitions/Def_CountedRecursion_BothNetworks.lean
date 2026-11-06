-- Prove2me | Definitions.Def_CountedRecursion_BothNetworks
-- name    : CountedRecursion_BothNetworks
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T09:12:57.489415+00:00
-- url     : https://prove2.me/theorems/2b10bcda-be7b-4d66-93a2-7e3b9daf55d4
-- title:
--   Both Networks
-- statement:
--   Definitions and structural lemmas for Both Networks, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/BothNetworks.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RowFactorRun
import Definitions.Def_CountedRecursion_ParentSize
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ K g lam B y x tq Lam : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}
end ExplicitCost


