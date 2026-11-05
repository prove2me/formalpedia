-- Prove2me | Definitions.Def_Eight_ViaGrouping_Main
-- name    : Eight_ViaGrouping_Main
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:52:11.116467+00:00
-- url     : https://prove2.me/theorems/3b6fd7da-c1c0-407c-9f2d-c21f9a7bb991
-- title:
--   Main
-- statement:
--   Definitions and structural lemmas for Main, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Main.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Search
import Definitions.Def_StepMachines_Math_RebalanceArith
import Mathlib.Tactic
set_option autoImplicit false
section
section
@[expose] section
namespace Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
namespace Cost
@[expose] noncomputable def Bp (K g P B : ℕ) : ℕ := ⌈2 * ((g : ℝ) * P) / K⌉₊ + g ^ 2 * B
section Model
variable {C : Type} [HasSize C] {Np : Procs C} {c : C} {g : ℕ} {N : Net g} {P B τ S : ℕ}
end Model
end Cost
open Cost
end Eight.ViaGrouping


