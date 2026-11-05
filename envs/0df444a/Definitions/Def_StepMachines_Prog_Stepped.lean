-- Prove2me | Definitions.Def_StepMachines_Prog_Stepped
-- name    : StepMachines_Prog_Stepped
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:18:39.775937+00:00
-- url     : https://prove2.me/theorems/8df50faa-7e1c-49fb-8064-dfcbc41b003c
-- title:
--   Stepped
-- statement:
--   Definitions and structural lemmas for Stepped, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachineStatements
set_option autoImplicit false
section
namespace Groundwork
section sizes
variable {α β : Type}
end sizes
namespace Stepped
variable {α β γ τ : Type}
@[expose] public def next (M : Stepped α β) (s : M.σ) : M.σ :=
  match M.out s with
  | some _ => s
  | none => M.step s
@[expose] public def run (M : Stepped α β) (a : α) (n : ℕ) : M.σ := M.next^[n] (M.init a)
@[expose] public def ofFun [HasSize α] [HasSize β] (f : α → β) : Stepped α β where
  σ := α ⊕ β
  init := .inl
  step s := match s with | .inl a => .inr (f a) | .inr b => .inr b
  out s := match s with | .inl _ => none | .inr b => some b
@[expose] public def mapIn (f : α → β) (M : Stepped β γ) : Stepped α γ where
  σ := M.σ
  init a := M.init (f a)
  step := M.step
  out := M.out
@[expose] public def mapOut (M : Stepped α β) (f : β → γ) : Stepped α γ where
  σ := M.σ
  init := M.init
  step := M.step
  out s := (M.out s).map f
@[expose] public def bind [HasSize α] (M : Stepped α β) (N : Stepped (α × β) γ) : Stepped α γ where
  σ := (α × M.σ) ⊕ N.σ
  init a := .inl (a, M.init a)
  step s := match s with
    | .inl p => match M.out p.2 with
      | some b => .inr (N.init (p.1, b))
      | none => .inl (p.1, M.step p.2)
    | .inr s => .inr (N.step s)
  out s := match s with | .inl _ => none | .inr s => N.out s
public inductive Orbit (nxt : τ → Option τ) : Option τ → List τ → Prop
  | nil : Orbit nxt none []
  | cons {x : τ} {xs : List τ} : Orbit nxt (nxt x) xs → Orbit nxt (some x) (x :: xs)
@[expose] public def foldGo (M : Stepped τ β) (c : γ) (x : Option τ) :
    (τ × γ × M.σ) ⊕ γ :=
  match x with
  | some x' => .inl (x', c, M.init x')
  | none => .inr c
@[expose] public def foldWhile [HasSize τ] [HasSize γ] (start : α → Option τ) (nxt : τ → Option τ)
    (M : Stepped τ β) (g : γ → τ → β → γ) (c₀ : α → γ) : Stepped α γ where
  σ := (τ × γ × M.σ) ⊕ γ
  init a := foldGo M (c₀ a) (start a)
  step s := match s with
    | .inl p => match M.out p.2.2 with
      | some b => foldGo M (g p.2.1 p.1 b) (nxt p.1)
      | none => .inl (p.1, p.2.1, M.step p.2.2)
    | .inr c => .inr c
  out s := match s with | .inl _ => none | .inr c => some c
section foldWhile
variable [HasSize τ] [HasSize γ] {start : α → Option τ} {nxt : τ → Option τ} {M : Stepped τ β}
  {g : γ → τ → β → γ} {c₀ : α → γ}
end foldWhile
end Stepped
end Groundwork


