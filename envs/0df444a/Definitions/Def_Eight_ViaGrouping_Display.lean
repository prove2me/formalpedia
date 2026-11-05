-- Prove2me | Definitions.Def_Eight_ViaGrouping_Display
-- name    : Eight_ViaGrouping_Display
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:51:15.173899+00:00
-- url     : https://prove2.me/theorems/06e7fda7-4cb4-48df-8fb5-fc17f061f9df
-- title:
--   Display
-- statement:
--   Definitions and structural lemmas for Display, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Display.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Table
import Definitions.Def_Eight_SecNetworks_Tables
import Definitions.Def_Eight_SecNetworks_Clique
set_option autoImplicit false
section
section
namespace Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
variable {C : Type} [HasSize C] {g K : ℕ}
def display (Np : Procs C) (c : C) (N : Net g) (hK0 : 0 < K) (x : ℕ) (γ : Fin K) (Θ : Fin K → List Bool) : ℤ :=
  (if ∀ γ', γ' ≠ γ → ∀ bit ∈ appendedBits (g := g) Np.toPaperNetwork c x γ γ' (Θ γ'), bit = false then 1 else 0) *
    ∑ z ∈ tuples (fun a => Paper.grouping hK0 x a = γ) N.S [],
      (∏ a with Paper.grouping hK0 x a = γ, N.W a (z a)) *
        (∏ p ∈ pairs (Fin g) with Paper.grouping hK0 x p.1 = γ ∧ Paper.grouping hK0 x p.2 = γ, N.Ψ p.1 p.2 (z p.1) (z p.2)) *
        ∏ p : Fin g × Fin g with Paper.grouping hK0 x p.1 = γ ∧ Paper.grouping hK0 x p.2 ≠ γ, N.f p.1 p.2 (z p.1) (thetaAt Np.toPaperNetwork c hK0 x Θ p.1 p.2)
variable {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}
end Eight.ViaGrouping


