-- Prove2me | Definitions.Def_ExplicitCost_SameRuns
-- name    : ExplicitCost_SameRuns
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T05:41:57.588932+00:00
-- url     : https://prove2.me/theorems/1ec79887-9095-4ea7-be4f-262fa0605f12
-- title:
--   Same Runs
-- statement:
--   Definitions and structural lemmas for Same Runs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_EntryDefs
import Definitions.Def_ExplicitCost_Mirror
import Mathlib.Tactic
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
namespace ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
variable (K g : ℕ)
def widenC (c : NetInput) : DataInput := ((unary K, unary g), c)
def widen (u : X0 NetInput) : X0 DataInput := ((widenC K g u.1.1, u.1.2), u.2)
abbrev widen₁ : X0 NetInput × ℕ → X0 DataInput × ℕ := Prod.map (widen K g) id
abbrev widen₂ : (X0 NetInput × ℕ) × ℕ → (X0 DataInput × ℕ) × ℕ := Prod.map (widen₁ K g) id
end ExplicitCost


