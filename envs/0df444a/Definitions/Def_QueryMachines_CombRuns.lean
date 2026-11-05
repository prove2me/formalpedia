-- Prove2me | Definitions.Def_QueryMachines_CombRuns
-- name    : QueryMachines_CombRuns
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T21:17:37.559655+00:00
-- url     : https://prove2.me/theorems/2f4a47f0-7314-49b9-920b-5eb4a5887e42
-- title:
--   Comb Runs
-- statement:
--   Definitions and structural lemmas for Comb Runs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/CombRuns.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombRunsStatement
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace QueryMachines.QueryMachine
open Groundwork Finset
variable {Q Q' A α α₁ α₂ β γ τ : Type}
section foldWhile
variable [HasSize τ] [HasSize γ] {start : α → Option τ} {nxt : τ → Option τ} {M : QueryMachine Q A τ β} {g : γ → τ → β → γ} {c₀ : α → γ} {O : Q → Option A}
end foldWhile
end QueryMachines.QueryMachine
namespace QueryMachines
open Groundwork Finset QueryMachine
end QueryMachines


