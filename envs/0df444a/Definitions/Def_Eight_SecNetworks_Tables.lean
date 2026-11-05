-- Prove2me | Definitions.Def_Eight_SecNetworks_Tables
-- name    : Eight_SecNetworks_Tables
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T21:11:41.875826+00:00
-- url     : https://prove2.me/theorems/2dc7da63-1c7d-4ebe-9cdd-a75b92c3bf1e
-- title:
--   Sec Networks Tables
-- statement:
--   Definitions and structural lemmas for Sec Networks Tables, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Tables.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecNetworks_LemGrouping
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_NetVal
import Mathlib.Tactic
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
namespace Eight.SecNetworks
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Paper
variable {C : Type} {g K : ℕ}
def appendedBits (Np : NetworkProcedures C) (c : C) (x : ℕ) (γ γ' : Fin K) (θ : List Bool) : List Bool :=
  θ.drop (lbLen K g Np c x (min γ γ').val (max γ γ').val)
def thetaAt (Np : NetworkProcedures C) (c : C) (hK0 : 0 < K) (x : ℕ) (Θ : Fin K → List Bool) (a b : Fin g) : List Bool :=
  mdec K g Np c x (min (grouping hK0 x a) (grouping hK0 x b)) (max (grouping hK0 x a) (grouping hK0 x b)) (Θ (grouping hK0 x b))
    (if grouping hK0 x a < grouping hK0 x b then (a, b) else (b, a))
end Eight.SecNetworks
end
section
@[expose] section
namespace Eight.SecNetworks
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Paper
variable {C : Type} {g K : ℕ}
end Eight.SecNetworks


