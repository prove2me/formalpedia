-- Prove2me | Definitions.Def_StepMachines_Math_SparsifyTree
-- name    : StepMachines_Math_SparsifyTree
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:17:10.909106+00:00
-- url     : https://prove2.me/theorems/7017eeab-2104-4f15-b33b-a20982140ee7
-- title:
--   Sparsify Tree
-- statement:
--   Definitions and structural lemmas for Sparsify Tree, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SparsifyTree.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Logic.Function.Iterate
set_option autoImplicit false
section
namespace Groundwork.Sparsify
open Finset
variable {σ : Type*} (step : σ → Option (σ × σ))
@[expose] public def leaves : ℕ → σ → List σ
  | 0, s => [s]
  | k + 1, s =>
    match step s with
    | none => [s]
    | some (l, h) => leaves k l ++ leaves k h
@[expose] public def round : List σ × List σ → List σ × List σ
  | ([], out) => ([], out)
  | (s :: r, out) =>
    match step s with
    | none => (r, s :: out)
    | some (l, h) => (l :: h :: r, out)
@[expose] public def roundB (test : σ → Bool) : List σ × Bool → List σ × Bool
  | ([], b) => ([], b)
  | (s :: r, b) =>
    match step s with
    | none => (r, test s || b)
    | some (l, h) => (l :: h :: r, b)
section Budget
variable {step} {G : σ → ℕ → ℕ → Prop} {D T q : ℕ}
def StackOK (G : σ → ℕ → ℕ → Prop) : List σ → Prop
  | [] => True
  | s :: r => (∃ p t, G s p t ∧ r.length ≤ p) ∧ StackOK G r
theorem StackOK.round
    (hs : ∀ s p t l h, G s p t → step s = some (l, h) → G l (p + 1) t ∧ G h (p + 1) (t + q))
    (st : List σ × List σ) (h : StackOK G st.1) : StackOK G (round step st).1 := by
  obtain ⟨_ | ⟨s, r⟩, out⟩ := st
  · exact h
  · obtain ⟨⟨p, t, hG, hp⟩, hr⟩ := h
    rw [Sparsify.round]
    split
    · exact hr
    · rename_i l h' h0
      obtain ⟨hl, hh⟩ := hs s p t l h' hG h0
      exact ⟨⟨p + 1, t, hl, by simpa using hp⟩, ⟨p + 1, t + q, hh, by omega⟩, hr⟩
end Budget
end Groundwork.Sparsify


