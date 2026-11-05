-- Prove2me | Definitions.Def_CircuitLowerBound_Interfaces
-- name    : CircuitLowerBound_Interfaces
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T17:51:53.425131+00:00
-- url     : https://prove2.me/theorems/9655fdbb-8ef6-41a1-ac1b-a5a1d6cad00a
-- title:
--   Interfaces
-- statement:
--   Definitions and structural lemmas for Interfaces, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Interfaces.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Defs
set_option autoImplicit false
section
section
namespace CircuitLowerBound
open ENP Groundwork Turing
def StTab : Prop := ∀ N : TM2ComputableAux Bool Bool, (∀ k, Finite (N.tm.Γ k)) →
  ∃ e : MCode, ∀ L P : ℕ, Fits e L P → (Sat (tabF e L P) ↔ Acc N P (2 ^ bt e L))
def StCode : Prop := ∀ (e : MCode) (a₀ : ℕ), ∃ a, a₀ ≤ a ∧ codeOf a = e
def StChain : Prop := ∀ a s : ℕ, nu (2 ^ a * (2 * s + 1)) = a ∧ pos (2 ^ a * (2 * s + 1)) = s
def StVars : Prop := ∀ (e : MCode) (L P : ℕ), Fits e L P → ∀ C ∈ tabF e L P, ∀ l ∈ C, l.1 < 2 ^ L
def StGreedy : Prop := ∀ (φ : Cnf) (M : ℕ), (∀ C ∈ φ, ∀ l ∈ C, l.1 < M) → Sat φ →
  ∀ C ∈ φ, ∃ l ∈ C, (greedy φ (l.1 + 1)).getD l.1 false = l.2
def StAlg : Prop := ∀ c₀ : ℕ, ∃ N : TM2ComputableAux Bool Bool, (∀ k, Finite (N.tm.Γ k)) ∧
  (∀ m T : ℕ, Acc N m T → Sat (Phi m)) ∧
  ∀ e : MCode, ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → codeOf (nu m) = e → pos m ≤ top (nu m) →
    ∀ C : Circuit, C.length ≤ c₀ * (m + 1) → (∀ D ∈ Phi m, ∃ l ∈ D, eval C (toWord m l.1) = l.2) → Acc N m (2 ^ (m / 8))
def StENP' : Prop := InENP' L0
def StENP : Prop := InENP L0
end CircuitLowerBound


