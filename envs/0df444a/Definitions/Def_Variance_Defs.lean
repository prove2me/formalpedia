-- Prove2me | Definitions.Def_Variance_Defs
-- name    : Variance_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:16:02.26538+00:00
-- url     : https://prove2.me/theorems/45b1ca0e-2ac3-42da-bd2b-2a2ddf753aaf
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Variance/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Theorems.Thm_Groundwork_PolyT_filter
attribute [local fun_prop] Groundwork.PolyT.filter


set_option autoImplicit false
section
section
namespace Variance
open Finset Eight.SecNetworks
variable {g K : ℕ}
def ordered (g : ℕ) : Finset (Fin g × Fin g) := univ.filter fun p => p.1 ≠ p.2
abbrev Contributes (γ γ' : Fin K) (χ : Fin g → Fin K) (p : Fin g × Fin g) : Prop := χ p.1 = γ ∧ χ p.2 = γ'
abbrev Meets (p q : Fin g × Fin g) : Prop := q.1 = p.1 ∨ q.1 = p.2 ∨ q.2 = p.1 ∨ q.2 = p.2
def cov (γ γ' : Fin K) (p q : Fin g × Fin g) : ℤ := (K : ℤ) ^ 4 * (#{χ : Fin g → Fin K | Contributes γ γ' χ p ∧ Contributes γ γ' χ q} : ℕ) - (K : ℤ) ^ g
def StYIsSum : Prop := ∀ (g K : ℕ) (c : Fin g → Fin g → ℕ) (χ : Fin g → Fin K) (γ γ' : Fin K), γ ≠ γ' →
  Y c χ γ γ' = ∑ p ∈ ordered g, if Contributes γ γ' χ p then c p.1 p.2 else 0
def StPairProb : Prop := ∀ (g K : ℕ) (γ γ' : Fin K), ∀ p ∈ ordered g, #{χ : Fin g → Fin K | Contributes γ γ' χ p} * K ^ 2 = K ^ g
def StMean : Prop := ∀ (g K : ℕ) (c : Fin g → Fin g → ℕ) (γ γ' : Fin K), γ ≠ γ' →
  (∑ χ : Fin g → Fin K, Y c χ γ γ') * K ^ 2 = K ^ g * ∑ a, ∑ b ∈ univ.erase a, c a b
def StVarIsSumOfCov : Prop := ∀ (g K : ℕ) (c : Fin g → Fin g → ℕ) (γ γ' : Fin K), γ ≠ γ' →
  ∑ χ : Fin g → Fin K, (((K ^ 2 : ℕ) : ℤ) * (Y c χ γ γ' : ℕ) - ((∑ a, ∑ b ∈ univ.erase a, c a b : ℕ) : ℤ)) ^ 2
    = ∑ p ∈ ordered g, ∑ q ∈ ordered g, ((c p.1 p.2 : ℕ) : ℤ) * ((c q.1 q.2 : ℕ) : ℤ) * cov γ γ' p q
def StCovDisjoint : Prop := ∀ (g K : ℕ) (γ γ' : Fin K), ∀ p ∈ ordered g, ∀ q ∈ ordered g, ¬ Meets p q → cov γ γ' p q = 0
def StCovLeOne : Prop := ∀ (g K : ℕ) (γ γ' : Fin K) (p q : Fin g × Fin g), cov γ γ' p q ≤ (K : ℤ) ^ 4 * (K : ℤ) ^ g
def StMeeting : Prop := ∀ (g P : ℕ) (c : Fin g → Fin g → ℕ), (∀ a b, c a b = c b a) → (∀ a, ∑ b ∈ univ.erase a, c a b ≤ P) → ∀ p : Fin g × Fin g,
  ∑ q ∈ ordered g with Meets p q, c q.1 q.2 ≤ 4 * P
def StVar : Prop := ∀ (g K P : ℕ) (c : Fin g → Fin g → ℕ), (∀ a b, c a b = c b a) → (∀ a, ∑ b ∈ univ.erase a, c a b ≤ P) → ∀ γ γ' : Fin K, γ ≠ γ' →
  ∑ χ : Fin g → Fin K, (((K ^ 2 : ℕ) : ℤ) * (Y c χ γ γ' : ℕ) - ((∑ a, ∑ b ∈ univ.erase a, c a b : ℕ) : ℤ)) ^ 2
    ≤ ((4 * P * (∑ a, ∑ b ∈ univ.erase a, c a b) * K ^ 4 * K ^ g : ℕ) : ℤ)
def StHence : Prop := ∀ (g P : ℕ) (c : Fin g → Fin g → ℕ), (∀ a b, c a b = c b a) → (∀ a, ∑ b ∈ univ.erase a, c a b ≤ P) → ∀ (κ : Fin g × Fin g → Fin g × Fin g → ℤ) (m : ℤ), 0 ≤ m →
  (∀ p ∈ ordered g, ∀ q ∈ ordered g, ¬ Meets p q → κ p q = 0) → (∀ p q, κ p q ≤ m) →
  ∑ p ∈ ordered g, ∑ q ∈ ordered g, ((c p.1 p.2 : ℕ) : ℤ) * ((c q.1 q.2 : ℕ) : ℤ) * κ p q ≤ ((4 * P * (∑ a, ∑ b ∈ univ.erase a, c a b) : ℕ) : ℤ) * m
def StVarOf : Prop := StVarIsSumOfCov → StCovDisjoint → StCovLeOne → StHence → StVar
def StSoMean : Prop := StYIsSum → StPairProb → StMean
def StTotalLe : Prop := ∀ (g P : ℕ) (c : Fin g → Fin g → ℕ), (∀ a, ∑ b ∈ univ.erase a, c a b ≤ P) → ∑ a, ∑ b ∈ univ.erase a, c a b ≤ g * P
def VarBound {g K : ℕ} (c : Fin g → Fin g → ℕ) (P : ℕ) (γ γ' : Fin K) : Prop :=
  ∑ χ : Fin g → Fin K, (((K ^ 2 : ℕ) : ℤ) * (Y c χ γ γ' : ℕ) - ((∑ a, ∑ b ∈ univ.erase a, c a b : ℕ) : ℤ)) ^ 2 ≤ ((4 * P * (∑ a, ∑ b ∈ univ.erase a, c a b) * K ^ 4 * K ^ g : ℕ) : ℤ)
def ChebBound {g K : ℕ} (c : Fin g → Fin g → ℕ) (P : ℕ) (γ γ' : Fin K) : Prop :=
  g * #{χ : Fin g → Fin K | K * (∑ a, ∑ b ∈ univ.erase a, c a b) + g * P < K ^ 3 * Y c χ γ γ'} ≤ 4 * K ^ 6 * K ^ g
def StChebOfVar : Prop := ∀ (g K P : ℕ) (c : Fin g → Fin g → ℕ) (γ γ' : Fin K), γ ≠ γ' → VarBound c P γ γ' → ∑ a, ∑ b ∈ univ.erase a, c a b ≤ g * P → ChebBound c P γ γ'
def StSomePairOfCheb : Prop := ∀ (g K P : ℕ) (c : Fin g → Fin g → ℕ), 1 ≤ K → (∀ a b, c a b = c b a) → (∀ γ γ' : Fin K, γ ≠ γ' → ChebBound c P γ γ') →
  g * #{χ : Fin g → Fin K | ∃ γ γ', γ ≠ γ' ∧ K * (∑ a, ∑ b ∈ univ.erase a, c a b) + g * P < K ^ 3 * Y c χ γ γ'} < 2 * K ^ 8 * K ^ g
def StGroupingOf : Prop := StVar → StTotalLe → StChebOfVar → StSomePairOfCheb → GroupingFacts
def StSearchOfGrouping : Prop := GroupingFacts → Eight.ViaGrouping.StSearch
end Variance


