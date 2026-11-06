-- Prove2me | Definitions.Def_CountedRecursion_Meets
-- name    : CountedRecursion_Meets
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:59:11.989994+00:00
-- url     : https://prove2.me/theorems/3ff532de-367a-4897-a6d0-3d10252adf84
-- title:
--   Meets
-- statement:
--   Definitions and structural lemmas for Meets, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Meets.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverPattern
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {c x₀ l lam B j : ℕ}
end ExplicitCost


