-- Prove2me | Definitions.Def_ClauseBound_Inst_HalfVal
-- name    : ClauseBound_Inst_HalfVal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:45:38.020047+00:00
-- url     : https://prove2.me/theorems/d35eb6df-c5ee-4ae8-8f79-5b214133347c
-- title:
--   Half Val
-- statement:
--   Definitions and structural lemmas for Half Val, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfVal.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
namespace ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec Finset
def StTopF : Prop := ∀ (pad : U) (h : ℕ), 1 ≤ h → padLen h ≤ pad.length → ∀ μ ∈ (allTab (4 * h)).flatten, μ.sum = h → ∀ i ≤ 2 * h, ∀ r : ℤ,
  ∀ π ∈ (allTab (4 * h)).flatten, ∀ σ ∈ (allTab (4 * h)).flatten,
    topF pad (4 * h) (allTab (4 * h)).flatten h μ i r π σ = ClauseBound.Boson.topK μ h i r (π : Multiset ℕ) (σ : Multiset ℕ)
def StBotF : Prop := ∀ (pad : U) (h : ℕ), 1 ≤ h → padLen h ≤ pad.length → ∀ μ ∈ (allTab (4 * h)).flatten, μ.sum = h → ∀ r : ℤ,
  ∀ π ∈ (allTab (4 * h)).flatten, ∀ σ ∈ (allTab (4 * h)).flatten,
    botF pad (4 * h) (allTab (4 * h)).flatten h μ r π σ = ClauseBound.Boson.botK μ h r (π : Multiset ℕ) (σ : Multiset ℕ)
namespace Val
end Val
open Val
end ClauseBound.Inst.Half


