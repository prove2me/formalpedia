-- Prove2me | Definitions.Def_UniformInK_Spars_Defs
-- name    : UniformInK_Spars_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:34:55.798461+00:00
-- url     : https://prove2.me/theorems/abbc58bf-c678-4ae6-8282-769e2357965a
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_SparsifyWidthK_ProgMain
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_filter
attribute [local fun_prop] Groundwork.PolyT.filter


set_option autoImplicit false
section
section
namespace UniformInK
open Finset Groundwork Groundwork.Sparsify WidthK WidthK.Prog
variable {α : Type*} [DecidableEq α]
structure AddU (θ : ℕ → ℕ) (F A : Finset (Finset α)) (r : ℕ) : Prop where
  ssub : ∀ D ∈ A, ∃ C ∈ F, D ⊂ C
  size : ∀ D ∈ A, D.card = r
  pos : 0 < r
  deg : ∀ Y : Finset α, Y.Nonempty → Y.card ≤ r → (Sparsify.over F r Y).card + (A.filter fun D => Y ⊆ D).card ≤ 2 * θ (r - Y.card)
structure InvU (θ : ℕ → ℕ) (F N : Finset (Finset α)) (a : ℕ → ℕ) : Prop where
  red : Reduced F
  sub : N ⊆ F
  deg : ∀ i (Y : Finset α), Y.Nonempty → Y.card ≤ i → ((lay N i).filter fun C => Y ⊆ C).card ≤ 2 * θ (i - Y.card)
  acc : ∀ i, a i ≤ (lay N i).card + ∑ i' ∈ range i, 2 * θ (i - i') * a i'
def NodeU (θ : ℕ → ℕ) (k τ : ℕ) (φ F : Finset (Finset α)) (p t : ℕ) : Prop :=
  (∀ C ∈ F, ∃ C' ∈ φ, C ⊆ C' ∧ (C'.Nonempty → C.Nonempty)) ∧
    ∃ (N : Finset (Finset α)) (a h : ℕ → ℕ), InvU θ F N a ∧ a 0 = 0 ∧ (∀ r, h r * θ r ≤ a r) ∧
      p ≤ ∑ i ∈ range k, a i ∧ t ≤ τ * ∑ r ∈ range k, h r
structure ThrU (k τ : ℕ) (θ β : ℕ → ℕ) : Prop where
  pos : ∀ i, 0 < θ i
  step : ∀ i, 0 < i → i < k → 4 * θ (i - 1) + ∑ i' ∈ range i, 2 * θ (i - i') * β i' ≤ β i
  mul : ∀ r, τ * β r ≤ θ r
def thetaU (τ : ℕ) : ℕ → ℕ
  | 0 => 1
  | i + 1 => 4 * τ ^ (2 * i + 1)
def betaSU (τ : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => 4 * τ ^ (2 * i)
def bsumU (τ k : ℕ) : ℕ := τ ^ (2 * k)
def leafCU (τ k : ℕ) : ℕ := 2 * ∑ j ∈ range k, thetaU τ j
def StNodeRootU : Prop := ∀ (α : Type) [DecidableEq α] (θ : ℕ → ℕ) (k τ : ℕ) (φ : Finset (Finset α)), NodeU θ k τ φ (Sparsify.red φ) 0 0
def StNodeStepU : Prop := ∀ (α : Type) [DecidableEq α] (θ : ℕ → ℕ) (k τ : ℕ) (φ F : Finset (Finset α)) (p t j : ℕ) (H : Finset α),
  (∀ i, 1 ≤ θ i) → NodeU θ k τ φ F p t → Rule θ k F j H →
    NodeU θ k τ φ (light F H) (p + 1) t ∧ NodeU θ k τ φ (heavy F j H) (p + 1) (t + τ)
def StNodeBoundU : Prop := ∀ (α : Type) [DecidableEq α] (θ β : ℕ → ℕ) (k τ n : ℕ) (φ F : Finset (Finset α)) (U : Finset α) (p t : ℕ),
  ThrU k τ θ β → U.card ≤ 2 * n → (∀ C ∈ φ, C ⊆ U) → NodeU θ k τ φ F p t → p ≤ (∑ i ∈ range k, β i) * n ∧ t ≤ k * n
def StThrU : Prop := ∀ k τ : ℕ, 1 ≤ k → 8 * k ≤ τ → ThrU k τ (thetaU τ) (betaSU τ)
def StBetaSumU : Prop := ∀ τ k : ℕ, 2 ≤ τ → ∑ i ∈ range k, betaSU τ i ≤ bsumU τ k
def StIfaceU : Prop := ∀ τ k n : ℕ, 1 ≤ k → 8 * k ≤ τ →
  Iface (thetaU τ) k (bsumU τ k * n) (k * n) τ (leafCU τ k * n) (ProgMain.Ok k n) (fun F₀ F p t => ProgMain.Ok k n F₀ ∧ NodeU (thetaU τ) k τ F₀ F p t)
end UniformInK


