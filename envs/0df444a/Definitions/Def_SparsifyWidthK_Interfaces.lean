-- Prove2me | Definitions.Def_SparsifyWidthK_Interfaces
-- name    : SparsifyWidthK_Interfaces
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:31:52.602953+00:00
-- url     : https://prove2.me/theorems/9f435a8a-82db-4166-bba2-e8bcccb85665
-- title:
--   Interfaces
-- statement:
--   Definitions and structural lemmas for Interfaces, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Interfaces.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Defs
import Definitions.Def_SparsifyWidthK_DefsProg
import Definitions.Def_ToTuring_Poly_Sparsify
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
namespace WidthK
open Finset Groundwork Groundwork.Sparsify WidthK.Prog
def StNodeRoot : Prop := ∀ (α : Type) [DecidableEq α] (θ : ℕ → ℕ) (k τ : ℕ) (φ : Finset (Finset α)), Node θ k τ φ (Sparsify.red φ) 0 0
def StNodeStep : Prop := ∀ (α : Type) [DecidableEq α] (θ : ℕ → ℕ) (k τ : ℕ) (φ F : Finset (Finset α)) (p t j : ℕ) (H : Finset α),
  (∀ i, 1 ≤ θ i) → Node θ k τ φ F p t → Rule θ k F j H →
    Node θ k τ φ (light F H) (p + 1) t ∧ Node θ k τ φ (heavy F j H) (p + 1) (t + τ)
def StNodeBound : Prop := ∀ (α : Type) [DecidableEq α] (θ β : ℕ → ℕ) (k τ n : ℕ) (φ F : Finset (Finset α)) (U : Finset α) (p t : ℕ),
  Thr τ θ β → U.card ≤ 2 * n → (∀ C ∈ φ, C ⊆ U) → Node θ k τ φ F p t → p ≤ (∑ i ∈ range k, β i) * n ∧ t ≤ k * n
def StLeafCard : Prop := ∀ (α : Type) [DecidableEq α] (θ : ℕ → ℕ) (k n : ℕ) (F : Finset (Finset α)) (U : Finset α),
  (∀ i, 1 ≤ θ i) → U.card ≤ 2 * n → (∀ C ∈ F, C ⊆ U ∧ C.Nonempty ∧ C.card ≤ k) → Leaf θ k F → F.card ≤ (2 * ∑ j ∈ range k, θ j) * n
def StLightEq : Prop := ∀ (α : Type) [DecidableEq α] (θ : ℕ → ℕ) (F : Finset (Finset α)) (j : ℕ) (H : Finset α),
  (∀ i, 1 ≤ θ i) → Reduced F → Heart θ F j H → light F H = {H} ∪ F.filter fun C => ¬ H ⊆ C
def StHeavyEq : Prop := ∀ (α : Type) [DecidableEq α] (θ : ℕ → ℕ) (F : Finset (Finset α)) (j : ℕ) (H : Finset α),
  Reduced F → Heart θ F j H → heavy F j H = petals F j H ∪ F.filter fun C => ∀ D ∈ petals F j H, ¬ D ⊆ C
def StSatIff : Prop := ∀ (α : Type) [DecidableEq α] (F : Finset (Finset α)) (j : ℕ) (H : Finset α) (v : α → Prop),
  Sat v F ↔ Sat v (light F H) ∨ Sat v (heavy F j H)
def StThr : Prop := ∀ τ : ℕ, 1 ≤ τ → Thr τ (theta τ) (beta τ)
def StBetaSum : Prop := ∀ τ k : ℕ, ∑ i ∈ range k, beta τ i ≤ bsum τ k
def StLeafCount : Prop := ∀ (k τ : ℕ) (ε : ℝ), 1 ≤ τ → ((k : ℝ) / τ) * Real.logb 2 (Real.exp 1 * τ * bsum τ k) ≤ ε →
  ∀ n : ℕ, ((∑ j ∈ range (k * n / τ + 1), (bsum τ k * n).choose j : ℕ) : ℝ) ≤ (2 : ℝ) ^ (ε * n)
def StExistsTau : Prop := ∀ (k τ₀ : ℕ) (ε : ℝ), 0 < ε →
  ∃ τ : ℕ, τ₀ ≤ τ ∧ 4 ≤ τ ∧ ((k : ℝ) / τ) * Real.logb 2 (Real.exp 1 * τ * bsum τ k) ≤ ε
structure Iface (θ : ℕ → ℕ) (k D T q leafB : ℕ) (Ok : Finset (Finset PLit) → Prop)
    (Node : Finset (Finset PLit) → Finset (Finset PLit) → ℕ → ℕ → Prop) : Prop where
  root : ∀ F₀, Ok F₀ → Node F₀ (red F₀) 0 0
  step : ∀ F₀ F p t j H, Node F₀ F p t → Rule θ k F j H → Node F₀ (light F H) (p + 1) t ∧ Node F₀ (heavy F j H) (p + 1) (t + q)
  bound : ∀ F₀ F p t, Node F₀ F p t → p ≤ D ∧ t ≤ T
  clause : ∀ F₀ F p t, Node F₀ F p t → ∀ C ∈ F, ∃ C₀ ∈ F₀, C ⊆ C₀
  leaf : ∀ F₀ F p t, Node F₀ F p t → Leaf θ k F → F.card ≤ leafB
  sat : ∀ F₀ F p t j H (v : PLit → Prop), Node F₀ F p t → Rule θ k F j H → (Sat v F ↔ Sat v (light F H) ∨ Sat v (heavy F j H))
  light_eq : ∀ F₀ F p t j H, Node F₀ F p t → Rule θ k F j H → light F H = {H} ∪ F.filter fun C => ¬ H ⊆ C
  heavy_eq : ∀ F₀ F p t j H, Node F₀ F p t → Rule θ k F j H →
    heavy F j H = petals F j H ∪ F.filter fun C => ∀ D ∈ petals F j H, ¬ D ⊆ C
structure Refines (θ : ℕ → ℕ) (k : ℕ) : Prop where
  some : ∀ s H P, NF s → pickK θ k s = some (H, P) →
    ∃ j, Rule θ k (toFin s) j H.toFinset ∧ toFin P = petals (toFin s) j H.toFinset ∧ NF P ∧ H.Nodup
  none : ∀ s, NF s → pickK θ k s = none → Leaf θ k (toFin s)
  nf_root : ∀ ψ, NF (rootP ψ)
  toFin_root : ∀ ψ, toFin (rootP ψ) = red (toFin ψ)
def StRefines : Prop := ∀ (θ : ℕ → ℕ) (k : ℕ), (∀ i, 1 ≤ θ i) → Refines θ k
def StProg : Prop := ∀ (τ k n : ℕ), 1 ≤ τ → ∀ ψ : PFml, (∀ C ∈ ψ, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) →
  (leaves (stepK (theta τ) k) (bsum τ k * n) (rootP ψ)).length ≤ ∑ j ∈ range (k * n / τ + 1), (bsum τ k * n).choose j ∧
  (∀ x ∈ leaves (stepK (theta τ) k) (bsum τ k * n) (rootP ψ),
    stepK (theta τ) k x = none ∧ x.length ≤ leafC τ k * n ∧ ∀ C ∈ x, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) ∧
  (∀ v : PLit → Prop, (∀ C ∈ ψ, ∃ a ∈ C, v a) ↔ ∃ x ∈ leaves (stepK (theta τ) k) (bsum τ k * n) (rootP ψ), ∀ C ∈ x, ∃ a ∈ C, v a) ∧
  ∀ i, ((round (stepK (theta τ) k))^[i] ([rootP ψ], [])).1.length ≤ bsum τ k * n + 1 ∧
    ∀ x ∈ ((round (stepK (theta τ) k))^[i] ([rootP ψ], [])).1, x.length ≤ ψ.length * 2 ^ k ∧
      ∀ C ∈ x, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n
def StCertStep : Prop := ∀ (θ : ℕ → ℕ) (k : ℕ), PolyT (stepK θ k)
end WidthK


