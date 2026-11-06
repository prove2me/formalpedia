-- Prove2me | Definitions.Def_Eight_ViaGrouping_CorDefs2
-- name    : Eight_ViaGrouping_CorDefs2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:18:09.960443+00:00
-- url     : https://prove2.me/theorems/438e1881-aea5-4a04-bf50-ecf66f9aaad1
-- title:
--   Cor Defs2
-- statement:
--   Definitions and structural lemmas for Cor Defs2, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/CorDefs2.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_Defs
import Definitions.Def_Eight_ViaGrouping_AlgDefs
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
namespace Eight.ViaGrouping
open Groundwork Groundwork.Prog Paper CountKSat GraphProblems
def EngineCounts (En : ℕ → ℕ → ℕ → StepMachine (List Unit × Fml) (List Bool)) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ δ : ℝ, 0 < δ → ∃ ℓ τ : ℕ, PolyTimeSteps (En k ℓ τ) ∧ ∃ c : ℕ, Serves (En k ℓ τ) k δ c
def Decides (M : StepMachine (List Bool) Bool) (k : ℕ) (δ : ℝ) (c : ℕ) : Prop := ∀ (n : ℕ) (φ : Sat3.CNF n), SatK.IsKCNF k φ →
  ∃ (T : ℕ) (b : Bool), M.Runs (SatK.enc k φ) T (c * ((SatK.enc k φ).length + 1) ^ c) b ∧ (b = true ↔ Sat3.Satisfiable φ) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n)
def verifier (M : StepMachine (List Bool) Bool) : StepMachine (List Bool) (List Bool) := Stepped.mapOut (Stepped.mapIn stripW M) fun b => [!b]
end Eight.ViaGrouping


