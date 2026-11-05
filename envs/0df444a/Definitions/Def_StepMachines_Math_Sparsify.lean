-- Prove2me | Definitions.Def_StepMachines_Math_Sparsify
-- name    : StepMachines_Math_Sparsify
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:16:18.92719+00:00
-- url     : https://prove2.me/theorems/262f2397-40a8-49e9-87af-2b67a2dd53fa
-- title:
--   Sparsify
-- statement:
--   Definitions and structural lemmas for Sparsify, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Sparsify.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.Order.Ring.Nat
set_option autoImplicit false
section
namespace Groundwork.Sparsify
open Finset
variable {α : Type*} [DecidableEq α]
@[expose] public def Sat (v : α → Prop) (F : Finset (Finset α)) : Prop := ∀ C ∈ F, ∃ l ∈ C, v l
@[expose] public def Reduced (F : Finset (Finset α)) : Prop := ∀ C ∈ F, ∀ D ∈ F, D ⊆ C → D = C
@[expose] public def red (F : Finset (Finset α)) : Finset (Finset α) := F.filter fun C => ∀ D ∈ F, D ⊆ C → D = C
@[expose] public def over (F : Finset (Finset α)) (i : ℕ) (S : Finset α) : Finset (Finset α) :=
  F.filter fun C => C.card = i ∧ S ⊆ C
@[expose] public def ones (F : Finset (Finset α)) : Finset (Finset α) := F.filter fun C => C.card = 1
section Add
variable {τ : ℕ} {F A : Finset (Finset α)}
end Add
structure Inv (τ : ℕ) (F N : Finset (Finset α)) : Prop where
  red : Reduced F
  sub : N ⊆ F
  two : ∀ C ∈ N, C.card = 2
  deg : ∀ a, (N.filter fun C => a ∈ C).card ≤ τ
section Step
variable {τ : ℕ} {F A N : Finset (Finset α)}
end Step
section Branch
variable {τ : ℕ} {F P : Finset (Finset α)} {H : Finset α}
end Branch
public def Node (τ : ℕ) (φ F : Finset (Finset α)) (p q : ℕ) : Prop :=
  (∀ C ∈ F, ∃ C' ∈ φ, C ⊆ C' ∧ (C'.Nonempty → C.Nonempty)) ∧
    ∃ N, Inv τ F N ∧ p ≤ N.card + (τ + 1) * (ones F).card ∧ q ≤ N.card + 2 * τ * (ones F).card
section Node
variable {τ : ℕ} {φ F P : Finset (Finset α)} {H : Finset α} {p q : ℕ}
end Node
section Count
variable {τ n : ℕ} {φ F : Finset (Finset α)} {p q : ℕ} {U : Finset α}
end Count
end Groundwork.Sparsify


