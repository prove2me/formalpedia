-- Prove2me | Definitions.Def_Value_Blocks
-- name    : Value_Blocks
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:01:54.033473+00:00
-- url     : https://prove2.me/theorems/421ff7b4-91a8-4d3b-a3e6-03a51a5d9d3b
-- title:
--   Blocks
-- statement:
--   Definitions and structural lemmas for Blocks, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Blocks.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Words
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_NetVal
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
@[expose] section
namespace Value
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Eight.SecNetworks Eight.ViaGrouping
variable {C : Type} [HasSize C] {g K : ℕ}
variable {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}
abbrev EdgeReads (Np : Procs C) (c : C) (hK0 : 0 < K) (x L : ℕ) (θ : Fin g × Fin g → List Bool) (p : Fin K × Fin K) (w : List Bool) : Prop :=
  (p.1 < p.2 → w ∈ mD K g Np.toPaperNetwork c x L p.1 p.2 ∧
    ∀ q : Fin g × Fin g, Paper.grouping hK0 x q.1 = p.1 ∧ Paper.grouping hK0 x q.2 = p.2 → mdec K g Np.toPaperNetwork c x p.1 p.2 w q = θ (pr q.1 q.2)) ∧ (¬ p.1 < p.2 → w = [])
end Value


