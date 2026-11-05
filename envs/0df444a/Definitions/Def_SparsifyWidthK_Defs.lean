-- Prove2me | Definitions.Def_SparsifyWidthK_Defs
-- name    : SparsifyWidthK_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:23:25.887029+00:00
-- url     : https://prove2.me/theorems/32a34150-96f3-4e1e-9aa0-5305d12e0787
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_Sparsify
set_option autoImplicit false
section
section
namespace WidthK
open Finset Groundwork Groundwork.Sparsify
variable {α : Type*} [DecidableEq α]
def petals (F : Finset (Finset α)) (j : ℕ) (H : Finset α) : Finset (Finset α) := (Sparsify.over F j H).image (· \ H)
def light (F : Finset (Finset α)) (H : Finset α) : Finset (Finset α) := Sparsify.red (F ∪ {H})
def heavy (F : Finset (Finset α)) (j : ℕ) (H : Finset α) : Finset (Finset α) := Sparsify.red (F ∪ petals F j H)
def Heart (θ : ℕ → ℕ) (F : Finset (Finset α)) (j : ℕ) (H : Finset α) : Prop :=
  H.Nonempty ∧ H.card < j ∧ θ (j - H.card) ≤ (Sparsify.over F j H).card
structure Rule (θ : ℕ → ℕ) (k : ℕ) (F : Finset (Finset α)) (j : ℕ) (H : Finset α) : Prop where
  le : j ≤ k
  heart : Heart θ F j H
  minj : ∀ j' < j, ∀ H', ¬ Heart θ F j' H'
  maxH : ∀ H', H.card < H'.card → ¬ Heart θ F j H'
def Leaf (θ : ℕ → ℕ) (k : ℕ) (F : Finset (Finset α)) : Prop := ∀ j ≤ k, ∀ H, ¬ Heart θ F j H
def lay (N : Finset (Finset α)) (i : ℕ) : Finset (Finset α) := N.filter fun C => C.card = i
structure AddK (d : ℕ → ℕ) (F A : Finset (Finset α)) (r : ℕ) : Prop where
  ssub : ∀ D ∈ A, ∃ C ∈ F, D ⊂ C
  size : ∀ D ∈ A, D.card = r
  pos : 0 < r
  deg : ∀ y, (Sparsify.over F r {y}).card + (A.filter fun D => y ∈ D).card ≤ d r
structure InvK (d : ℕ → ℕ) (F N : Finset (Finset α)) (a : ℕ → ℕ) : Prop where
  red : Reduced F
  sub : N ⊆ F
  deg : ∀ i y, ((lay N i).filter fun C => y ∈ C).card ≤ d i
  acc : ∀ i, a i ≤ (lay N i).card + d i * ∑ i' ∈ range i, a i'
def nextN (N A : Finset (Finset α)) : Finset (Finset α) := A ∪ N.filter fun C => ∀ D ∈ A, ¬ D ⊆ C
def nextA (a : ℕ → ℕ) (r c : ℕ) : ℕ → ℕ := fun i => a i + if i = r then c else 0
def dg (θ : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => 2 * θ i
def Node (θ : ℕ → ℕ) (k τ : ℕ) (φ F : Finset (Finset α)) (p t : ℕ) : Prop :=
  (∀ C ∈ F, ∃ C' ∈ φ, C ⊆ C' ∧ (C'.Nonempty → C.Nonempty)) ∧
    ∃ (N : Finset (Finset α)) (a h : ℕ → ℕ), InvK (dg θ) F N a ∧ a 0 = 0 ∧ (∀ r, h r * θ r ≤ a r) ∧
      p ≤ ∑ i ∈ range k, a i ∧ t ≤ τ * ∑ r ∈ range k, h r
structure Thr (τ : ℕ) (θ β : ℕ → ℕ) : Prop where
  pos : ∀ i, 0 < θ i
  step : ∀ i, 2 * θ i * (2 + ∑ j ∈ range (i + 1), β j) ≤ β (i + 1)
  mul : ∀ r, τ * β r ≤ θ r
def thrPair (τ : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, 2)
  | i + 1 => (2 * τ * (thrPair τ i).1 * (thrPair τ i).2, (thrPair τ i).2 * (1 + 2 * (thrPair τ i).1))
def theta (τ i : ℕ) : ℕ := (thrPair τ i).1
def bsum (τ i : ℕ) : ℕ := (thrPair τ i).2
def beta (τ : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => 2 * theta τ i * bsum τ i
def leafC (τ k : ℕ) : ℕ := 2 * ∑ j ∈ range k, theta τ j
end WidthK


