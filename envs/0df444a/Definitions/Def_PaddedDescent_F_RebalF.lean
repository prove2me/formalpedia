-- Prove2me | Definitions.Def_PaddedDescent_F_RebalF
-- name    : PaddedDescent_F_RebalF
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:23:46.686834+00:00
-- url     : https://prove2.me/theorems/61b984a7-aa7e-4509-b498-cdc7e1842042
-- title:
--   Rebal F
-- statement:
--   Definitions and structural lemmas for Rebal F, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/RebalF.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Table
import Definitions.Def_StepMachines_Prog_NetRun
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_Groundwork_Net_Net
set_option autoImplicit false
section
section
@[expose] section
namespace PaddedDescent.F.RebalF
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Stepped Finset
def Halts {α β : Type} (M : Stepped α β) (a : α) (b : β) : Prop := ∃ T S, M.Runs a T S b
section hcalc
variable {α β : Type}
end hcalc
variable {C : Type}
def termP (K g : ℕ) (F : FNet C) (u : (X0 C × ℕ) × ℕ) : ℤ :=
  bif isOne K g u then 1
  else bif isW g u then F.W (qW K g F.toP u)
  else bif isPsi K g u then ∑ y ∈ range (nLab g F.toP u), F.f (qP1 K g F.toP (u, y)) * F.f (qP2 K g F.toP (u, y))
  else F.f (qF K g F.toP u)
def mergedP (K g : ℕ) (F : FNet C) (u : X0 C) : ℤ :=
  bif validB K g F.toP u then ∑ y ∈ range (nStates K g F.toP u), ∏ i ∈ range (g * g), termP K g F ((u, y), i) else 0
section
variable [HasSize C]
end
end PaddedDescent.F.RebalF


