-- Prove2me | Definitions.Def_QueryMachines_CombRunsStatement
-- name    : QueryMachines_CombRunsStatement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T21:12:26.752201+00:00
-- url     : https://prove2.me/theorems/4b5df48c-03a7-46d2-a769-b25df46ffefd
-- title:
--   Comb Runs Statement
-- statement:
--   Definitions and structural lemmas for Comb Runs Statement, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/CombRunsStatement.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombDefs
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
namespace QueryMachines
open Groundwork Finset
def StLiftRuns : Prop := ∀ (Q A α β : Type) (R : Stepped α β) (O : Q → Option A) (a : α) (t S : ℕ) (b : β),
  R.Runs a t S b → (QueryMachine.lift R : QueryMachine Q A α β).Runs O a t [] S b
def StQueryRuns : Prop := ∀ (Q A α : Type) [HasSize α] [HasSize A] (h : α → Q) (O : Q → Option A) (a : α) (v : A),
  O (h a) = some v → (QueryMachine.query h : QueryMachine Q A α A).Runs O a 0 [h a] (max (size a) (size v) + 1) v
def StMapAskRuns : Prop := ∀ (Q Q' A α β : Type) (h : Q → Q') (M : QueryMachine Q A α β) (O : Q' → Option A) (a : α) (own S : ℕ) (L : List Q) (b : β),
  M.Runs (fun x => O (h x)) a own L S b → (QueryMachine.mapAsk h M).Runs O a own (L.map h) S b
def StMapInRuns : Prop := ∀ (Q A α β γ : Type) (g : α → β) (M : QueryMachine Q A β γ) (O : Q → Option A) (a : α) (own S : ℕ) (L : List Q) (c : γ),
  M.Runs O (g a) own L S c → (QueryMachine.mapIn g M).Runs O a own L S c
def StMapOutRuns : Prop := ∀ (Q A α β γ : Type) (M : QueryMachine Q A α β) (g : β → γ) (O : Q → Option A) (a : α) (own S : ℕ) (L : List Q) (b : β),
  M.Runs O a own L S b → (QueryMachine.mapOut M g).Runs O a own L S (g b)
def StBindRuns : Prop := ∀ (Q A α β γ : Type) [HasSize α] (M : QueryMachine Q A α β) (N : QueryMachine Q A (α × β) γ) (O : Q → Option A) (a : α) (t t' S S' : ℕ) (L L' : List Q) (b : β) (c : γ),
  M.Runs O a t L S b → N.Runs O (a, b) t' L' S' c → (QueryMachine.bind M N).Runs O a (t + 1 + t') (L ++ L') (max (size a + S) S' + 1) c
def StBothRuns : Prop := ∀ (Q A α β γ : Type) [HasSize α] [HasSize β] (M : QueryMachine Q A α β) (N : QueryMachine Q A α γ) (O : Q → Option A) (a : α) (t t' S S' : ℕ) (L L' : List Q) (b : β) (c : γ),
  M.Runs O a t L S b → N.Runs O a t' L' S' c → (QueryMachine.both M N).Runs O a (t + 1 + t') (L ++ L') (max (size a + S) (size b + S') + 1) (b, c)
def StBranchRuns : Prop := ∀ (Q A α α₁ α₂ β : Type) (sel : α → α₁ ⊕ α₂) (M₁ : QueryMachine Q A α₁ β) (M₂ : QueryMachine Q A α₂ β) (O : Q → Option A) (a : α) (t S : ℕ) (L : List Q) (b : β),
  (∀ x, sel a = .inl x → M₁.Runs O x t L S b → (QueryMachine.branch sel M₁ M₂).Runs O a t L (S + 1) b) ∧
  (∀ y, sel a = .inr y → M₂.Runs O y t L S b → (QueryMachine.branch sel M₁ M₂).Runs O a t L (S + 1) b)
def StFoldWhileRuns : Prop := ∀ (Q A α β γ τ : Type) [HasSize τ] [HasSize γ] (start : α → Option τ) (nxt : τ → Option τ) (M : QueryMachine Q A τ β) (g : γ → τ → β → γ) (c₀ : α → γ) (O : Q → Option A)
    (a : α) (xs : List τ), Stepped.Orbit nxt (start a) xs → ∀ (t : τ → ℕ) (Lq : τ → List Q) (v : τ → β) (Sx Sc Sm : ℕ),
  (∀ x ∈ xs, M.Runs O x (t x) (Lq x) Sm (v x)) → (∀ x ∈ xs, size x ≤ Sx) → (∀ l, l <+: xs → size (l.foldl (fun c x => g c x (v x)) (c₀ a)) ≤ Sc) →
  (QueryMachine.foldWhile start nxt M g c₀).Runs O a (xs.map fun x => t x + 1).sum (xs.flatMap Lq) (Sx + (Sc + Sm) + 1) (xs.foldl (fun c x => g c x (v x)) (c₀ a))
def StFoldRangeRuns : Prop := ∀ (Q A α β γ : Type) [HasSize α] [HasSize γ] (N : α → ℕ) (M : QueryMachine Q A (α × ℕ) β) (g : γ → ℕ → β → γ) (c₀ : α → γ) (O : Q → Option A) (a : α)
    (t : ℕ → ℕ) (Lq : ℕ → List Q) (v : ℕ → β) (Sc Sm : ℕ),
  (∀ y < N a, M.Runs O (a, y) (t y) (Lq y) Sm (v y)) → (∀ k ≤ N a, size ((List.range k).foldl (fun c y => g c y (v y)) (c₀ a)) ≤ Sc) →
  (QueryMachine.foldRange N M g c₀).Runs O a (∑ y ∈ range (N a), (t y + 1)) ((List.range (N a)).flatMap Lq) (size a + size (N a) + (Sc + Sm) + 1) ((List.range (N a)).foldl (fun c y => g c y (v y)) (c₀ a))
end QueryMachines


