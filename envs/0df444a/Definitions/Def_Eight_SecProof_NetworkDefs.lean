-- Prove2me | Definitions.Def_Eight_SecProof_NetworkDefs
-- name    : Eight_SecProof_NetworkDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T21:19:36.895726+00:00
-- url     : https://prove2.me/theorems/3c0aa403-b024-49c9-9bdb-1ff6786a8089
-- title:
--   Sec Proof Network Defs
-- statement:
--   Definitions and structural lemmas for Sec Proof Network Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecProof_NetworkDefs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Paper_SecProof_Proof
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
namespace Eight
open Finset Groundwork Groundwork.Prog Groundwork.SatNet Paper
def occurring (Φ : Formula) : Finset ℕ := (Φ.flatten.map Prod.fst).toFinset
abbrev Assignment (Φ : Formula) : Type := {v : ℕ // v ∈ occurring Φ} → Bool
def Satisfies (Φ : Formula) (a : Assignment Φ) : Prop := ∀ C ∈ Φ, ∃ l ∈ C, ∃ h : l.1 ∈ occurring Φ, a ⟨l.1, h⟩ = l.2
instance (Φ : Formula) : DecidablePred (Satisfies Φ) := fun a => by unfold Satisfies; infer_instance
def numSat (Φ : Formula) : ℕ := #{a : Assignment Φ | Satisfies Φ a}
def continued {Φ : Formula} (a : Assignment Φ) (v : ℕ) : Bool := if h : v ∈ occurring Φ then a ⟨v, h⟩ else false
def occurrencesOf (Φ : Formula) (g μ k : ℕ) : Finset (Slot g μ k) := {p | lit Φ p ≠ none}
def testsOf (Φ : Formula) (g μ k : ℕ) : Finset (Slot g μ k × Slot g μ k) := {t | Link Φ t.1 t.2}
abbrev occurrences (g : ℕ) (Φ : Formula) : Finset (Slot g (clusterSize g Φ) 3) := occurrencesOf Φ g (clusterSize g Φ) 3
abbrev tests (g : ℕ) (Φ : Formula) : Finset (Slot g (clusterSize g Φ) 3 × Slot g (clusterSize g Φ) 3) := testsOf Φ g (clusterSize g Φ) 3
end Eight


