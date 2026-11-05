-- Prove2me | Definitions.Def_Exits_Runs
-- name    : Exits_Runs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:47:50.625681+00:00
-- url     : https://prove2.me/theorems/3d6b260f-3e31-4138-b1fb-6f38a36da5ea
-- title:
--   Runs
-- statement:
--   Definitions and structural lemmas for Runs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Runs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_Tested
import Definitions.Def_StepMachines_Prog_Range
import Definitions.Def_StepMachines_Prog_Range
import Definitions.Def_StepMachines_Prog_Walk
import Definitions.Def_StepMachines_Prog_Walk
set_option autoImplicit false
section
section
@[expose] section
namespace Exits
open Finset Groundwork Groundwork.Stepped
open Groundwork.Sparsify (leaves)
variable {α β γ τ ν : Type}
section foldUntil
variable [HasSize τ] [HasSize γ] {start : α → Option τ} {nxt : τ → Option τ} {M : Stepped τ β} {g : γ → τ → β → γ} {stop : γ → Bool} {c₀ : α → γ}
end foldUntil
end Exits


