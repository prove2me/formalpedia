-- Prove2me | Definitions.Def_QueryMachines_Kernel
-- name    : QueryMachines_Kernel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:45:28.735217+00:00
-- url     : https://prove2.me/theorems/a582a671-c1a9-4a4f-9c24-42c142ea4fea
-- title:
--   Kernel
-- statement:
--   Definitions and structural lemmas for Kernel, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Kernel.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_PolyT
set_option autoImplicit false
section
section
namespace QueryMachines
open Groundwork
variable {Q A Q' A' C α β : Type}
structure QueryMachine (Q A α β : Type) : Type 1 extends Stepped α β where
  ask : σ → Option Q
  resume : σ → A → σ
namespace QueryMachine
inductive Reaches (M : QueryMachine Q A α β) (O : Q → Option A) (S : ℕ) (b : β) : M.σ → ℕ → List Q → Prop
  | halt {s : M.σ} {own : ℕ} : M.out s = some b → size s ≤ S → Reaches M O S b s own []
  | step {s : M.σ} {own : ℕ} {L : List Q} : M.out s = none → M.ask s = none → size s ≤ S → Reaches M O S b (M.step s) own L →
      Reaches M O S b s (own + 1) L
  | query {s : M.σ} {own : ℕ} {L : List Q} {x : Q} {v : A} : M.out s = none → M.ask s = some x → O x = some v → size s ≤ S →
      Reaches M O S b (M.resume s v) own L → Reaches M O S b s own (x :: L)
def Runs (M : QueryMachine Q A α β) (O : Q → Option A) (a : α) (own : ℕ) (L : List Q) (S : ℕ) (b : β) : Prop := M.Reaches O S b (M.init a) own L
def Within (M : QueryMachine Q A α β) (O : Q → Option A) (w : Q → ℕ) (a : α) (T S : ℕ) (b : β) : Prop :=
  ∃ (own : ℕ) (L : List Q), M.Runs O a own L S b ∧ own + (L.map w).sum ≤ T
def WithinFrom (M : QueryMachine Q A α β) (O : Q → Option A) (w : Q → ℕ) (s : M.σ) (T S : ℕ) (b : β) : Prop :=
  ∃ (own : ℕ) (L : List Q), M.Reaches O S b s own L ∧ own + (L.map w).sum ≤ T
def unitCost : Q → ℕ := fun _ => 1
def close (M : QueryMachine Q A α β) (O : Q → Option A) : Stepped α β where
  σ := M.σ
  sz := M.sz
  init := M.init
  step s := match M.ask s with
    | some x => (match O x with | some v => M.resume s v | none => s)
    | none => M.step s
  out := M.out
def plug [HasSize C] (M : QueryMachine Q A α β) (R : Stepped (C × Q) A) : Stepped (C × α) β where
  σ := C × (M.σ ⊕ (M.σ × R.σ))
  init x := (x.1, .inl (M.init x.2))
  step s := match s.2 with
    | .inl m => (match M.ask m with
      | some x => (s.1, .inr (m, R.init (s.1, x)))
      | none => (s.1, .inl (M.step m)))
    | .inr p => (match R.out p.2 with
      | some v => (s.1, .inl (M.resume p.1 v))
      | none => (s.1, .inr (p.1, R.step p.2)))
  out s := match s.2 with | .inl m => M.out m | .inr _ => none
def subst [HasSize C] (M : QueryMachine Q A α β) (N : QueryMachine Q' A' (C × Q) A) : QueryMachine Q' A' (C × α) β where
  toStepped := M.plug N.toStepped
  ask := fun (s : C × (M.σ ⊕ (M.σ × N.σ))) => match s.2 with
    | .inl _ => none
    | .inr p => (match N.out p.2 with | some _ => none | none => N.ask p.2)
  resume := fun (s : C × (M.σ ⊕ (M.σ × N.σ))) v => match s.2 with
    | .inl _ => s
    | .inr p => (s.1, .inr (p.1, N.resume p.2 v))
class IsPolyQ [Enc Q] [Enc A] [Enc α] [Enc β] (M : QueryMachine Q A α β) where
  [enc : Enc M.σ]
  [carried : Carried M.σ]
  init : PolyT M.init
  step : PolyT M.step
  out : PolyT M.out
  ask : PolyT M.ask
  resume : PolyT fun p : M.σ × A => M.resume p.1 p.2
def PolyTimeSteps [Enc Q] [Enc A] [Enc α] [Enc β] (M : QueryMachine Q A α β) : Prop := Nonempty (IsPolyQ M)
end QueryMachine
def StMono : Prop := ∀ (Q A α β : Type) (M : QueryMachine Q A α β) (O : Q → Option A) (s : M.σ) (own own' S S' : ℕ) (L : List Q) (b : β),
  M.Reaches O S b s own L → own ≤ own' → S ≤ S' → M.Reaches O S' b s own' L
def StWithinRules : Prop := ∀ (Q A α β : Type) (M : QueryMachine Q A α β) (O : Q → Option A) (w : Q → ℕ) (s : M.σ) (T S : ℕ) (b : β),
  (M.out s = some b → size s ≤ S → M.WithinFrom O w s T S b) ∧
  (M.out s = none → M.ask s = none → size s ≤ S → M.WithinFrom O w (M.step s) T S b → M.WithinFrom O w s (T + 1) S b) ∧
  (∀ (x : Q) (v : A), M.out s = none → M.ask s = some x → O x = some v → size s ≤ S → M.WithinFrom O w (M.resume s v) T S b → M.WithinFrom O w s (T + w x) S b)
def StUnique : Prop := ∀ (Q A α β : Type) (M : QueryMachine Q A α β) (O : Q → Option A) (a : α) (own own' S S' : ℕ) (L L' : List Q) (b b' : β),
  M.Runs O a own L S b → M.Runs O a own' L' S' b' → b = b' ∧ L = L'
def StClose : Prop := ∀ (Q A α β : Type) (M : QueryMachine Q A α β) (O : Q → Option A) (a : α) (T S : ℕ) (b : β),
  (M.close O).Runs a T S b ↔ M.Within O QueryMachine.unitCost a T S b
def StQueriesLe : Prop := ∀ (Q A α β : Type) (M : QueryMachine Q A α β) (O : Q → Option A) (a : α) (T S : ℕ) (b : β),
  M.Within O QueryMachine.unitCost a T S b → ∃ (own : ℕ) (L : List Q), M.Runs O a own L S b ∧ own + L.length ≤ T
def StSlowDown : Prop := ∀ (Q A α β : Type) (M : QueryMachine Q A α β) (O : Q → Option A) (a : α) (T S t : ℕ) (b : β), 1 ≤ t →
  M.Within O QueryMachine.unitCost a T S b → M.Within O (fun _ => t) a (T * t) S b
def StPlug : Prop := ∀ (Q A C α β : Type) [HasSize C] (M : QueryMachine Q A α β) (R : Stepped (C × Q) A) (O : Q → Option A) (c : C) (a : α) (own S S' : ℕ) (L : List Q) (b : β) (t : Q → ℕ),
  M.Runs O a own L S b → (∀ x ∈ L, ∀ v, O x = some v → R.Runs (c, x) (t x) S' v) →
    (M.plug R).Runs (c, a) (own + (L.map fun x => t x + 2).sum) (size c + S + S' + 1) b
def StSubst : Prop := ∀ (Q A Q' A' C α β : Type) [HasSize C] (M : QueryMachine Q A α β) (N : QueryMachine Q' A' (C × Q) A) (O : Q → Option A) (O' : Q' → Option A') (c : C) (a : α) (own S S' : ℕ)
    (L : List Q) (b : β) (t : Q → ℕ) (L' : Q → List Q'),
  M.Runs O a own L S b → (∀ x ∈ L, ∀ v, O x = some v → N.Runs O' (c, x) (t x) (L' x) S' v) →
    (M.subst N).Runs O' (c, a) (own + (L.map fun x => t x + 2).sum) (L.flatMap L') (size c + S + S' + 1) b
def StSubstWithin : Prop := ∀ (Q A Q' A' C α β : Type) [HasSize C] (M : QueryMachine Q A α β) (N : QueryMachine Q' A' (C × Q) A) (O : Q → Option A) (O' : Q' → Option A') (w : Q → ℕ) (w' : Q' → ℕ) (c : C)
    (a : α) (T S S' : ℕ) (b : β) (t : Q → ℕ),
  M.Within O w a T S b → (∀ x v, O x = some v → N.Within O' w' (c, x) (t x) S' v) → (∀ x, t x + 2 ≤ w x) →
    (M.subst N).Within O' w' (c, a) T (size c + S + S' + 1) b
def StCloseSubst : Prop := ∀ (Q A Q' A' C α β : Type) [HasSize C] (M : QueryMachine Q A α β) (N : QueryMachine Q' A' (C × Q) A) (O' : Q' → Option A'),
  (M.subst N).close O' = M.plug (N.close O')
def StPolyPlug : Prop := ∀ (Q A C α β : Type) [Enc Q] [Enc A] [Enc α] [Enc β] [HasSize C] [Enc C] [Carried C] (M : QueryMachine Q A α β) (R : Stepped (C × Q) A),
  M.PolyTimeSteps → Nonempty (IsPolyT R) → Nonempty (IsPolyT (M.plug R))
def StPolySubst : Prop := ∀ (Q A Q' A' C α β : Type) [Enc Q] [Enc A] [Enc Q'] [Enc A'] [Enc α] [Enc β] [HasSize C] [Enc C] [Carried C] (M : QueryMachine Q A α β) (N : QueryMachine Q' A' (C × Q) A),
  M.PolyTimeSteps → N.PolyTimeSteps → (M.subst N).PolyTimeSteps
def StPolyClose : Prop := ∀ (Q A α β : Type) [Enc Q] [Enc A] [Enc α] [Enc β] (M : QueryMachine Q A α β) (O : Q → Option A),
  M.PolyTimeSteps → PolyT O → Nonempty (IsPolyT (M.close O))
end QueryMachines


