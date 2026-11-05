-- Prove2me | Definitions.Def_QueryMachines_CombDefs
-- name    : QueryMachines_CombDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T21:09:06.387491+00:00
-- url     : https://prove2.me/theorems/c4b034fb-f337-4694-8059-b050533293f5
-- title:
--   Comb Defs
-- statement:
--   Definitions and structural lemmas for Comb Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/CombDefs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_Kernel
import Definitions.Def_StepMachines_Prog_Range
import Definitions.Def_Eight_SecNetworks_LemGrouping
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_Unary_const
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
namespace Groundwork.Stepped
variable {α β : Type}
def ofOption [HasSize α] [HasSize β] (g : α → Option β) : Stepped α β where
  σ := α ⊕ β
  init := .inl
  step s := match s with | .inl a => (match g a with | some b => .inr b | none => .inl a) | .inr b => .inr b
  out s := match s with | .inl _ => none | .inr b => some b
end Groundwork.Stepped
namespace QueryMachines.QueryMachine
open Groundwork
variable {Q A Q' C α α₁ α₂ β γ δ ι τ : Type}
def lift (M : Stepped α β) : QueryMachine Q A α β := { M with ask := fun _ => none, resume := fun s _ => s }
def query [HasSize α] [HasSize A] (h : α → Q) : QueryMachine Q A α A where
  σ := α ⊕ A
  init := .inl
  step s := s
  out s := match s with | .inl _ => none | .inr b => some b
  ask s := match s with | .inl a => some (h a) | .inr _ => none
  resume _ v := .inr v
def mapAsk (h : Q → Q') (M : QueryMachine Q A α β) : QueryMachine Q' A α β :=
  { M.toStepped with ask := fun s => (M.ask s).map h, resume := M.resume }
def mapIn (g : α → β) (M : QueryMachine Q A β γ) : QueryMachine Q A α γ :=
  { Stepped.mapIn g M.toStepped with ask := M.ask, resume := M.resume }
def mapOut (M : QueryMachine Q A α β) (g : β → γ) : QueryMachine Q A α γ :=
  { Stepped.mapOut M.toStepped g with ask := M.ask, resume := M.resume }
def bind [HasSize α] (M : QueryMachine Q A α β) (N : QueryMachine Q A (α × β) γ) : QueryMachine Q A α γ :=
  { Stepped.bind M.toStepped N.toStepped with
    ask := fun (s : (α × M.σ) ⊕ N.σ) => match s with
      | .inl p => (match M.out p.2 with | some _ => none | none => M.ask p.2)
      | .inr s => N.ask s
    resume := fun (s : (α × M.σ) ⊕ N.σ) v => match s with
      | .inl p => (.inl (p.1, M.resume p.2 v) : (α × M.σ) ⊕ N.σ)
      | .inr s => .inr (N.resume s v) }
def foldWhile [HasSize τ] [HasSize γ] (start : α → Option τ) (nxt : τ → Option τ) (M : QueryMachine Q A τ β) (g : γ → τ → β → γ) (c₀ : α → γ) : QueryMachine Q A α γ :=
  { Stepped.foldWhile start nxt M.toStepped g c₀ with
    ask := fun (s : (τ × γ × M.σ) ⊕ γ) => match s with
      | .inl p => (match M.out p.2.2 with | some _ => none | none => M.ask p.2.2)
      | .inr _ => none
    resume := fun (s : (τ × γ × M.σ) ⊕ γ) v => match s with
      | .inl p => (.inl (p.1, p.2.1, M.resume p.2.2 v) : (τ × γ × M.σ) ⊕ γ)
      | .inr c => .inr c }
def branch (sel : α → α₁ ⊕ α₂) (M₁ : QueryMachine Q A α₁ β) (M₂ : QueryMachine Q A α₂ β) : QueryMachine Q A α β :=
  { Stepped.branch sel M₁.toStepped M₂.toStepped with
    ask := fun (s : M₁.σ ⊕ M₂.σ) => match s with | .inl s => M₁.ask s | .inr s => M₂.ask s
    resume := fun (s : M₁.σ ⊕ M₂.σ) v => match s with
      | .inl s => (.inl (M₁.resume s v) : M₁.σ ⊕ M₂.σ) | .inr s => .inr (M₂.resume s v) }
def both [HasSize α] [HasSize β] (M : QueryMachine Q A α β) (N : QueryMachine Q A α γ) : QueryMachine Q A α (β × γ) :=
  { Stepped.both M.toStepped N.toStepped with
    ask := fun (s : (α × M.σ) ⊕ (β × N.σ)) => match s with
      | .inl p => (match M.out p.2 with | some _ => none | none => M.ask p.2)
      | .inr p => N.ask p.2
    resume := fun (s : (α × M.σ) ⊕ (β × N.σ)) v => match s with
      | .inl p => (.inl (p.1, M.resume p.2 v) : (α × M.σ) ⊕ (β × N.σ))
      | .inr p => .inr (p.1, N.resume p.2 v) }
def ite (p : α → Bool) (M N : QueryMachine Q A α β) : QueryMachine Q A α β := branch (Stepped.iteSel p) M N
def const [HasSize α] [HasSize β] (b : β) : QueryMachine Q A α β := lift (Stepped.const b)
def optBind [HasSize α] [HasSize β] (M : QueryMachine Q A α (Option ι)) (N : QueryMachine Q A (α × ι) β) (dflt : α → β) : QueryMachine Q A α β :=
  bind M (branch Stepped.optSel N (lift (Stepped.ofFun dflt)))
def foldRange [HasSize α] [HasSize γ] (N : α → ℕ) (M : QueryMachine Q A (α × ℕ) β) (g : γ → ℕ → β → γ) (c₀ : α → γ) : QueryMachine Q A α γ :=
  foldWhile (Stepped.rangeStart N) (Stepped.rangeNext N) M (Stepped.rangeG g) c₀
def sumRange [HasSize α] (N : α → ℕ) (M : QueryMachine Q A (α × ℕ) ℤ) : QueryMachine Q A α ℤ := foldRange N M Stepped.addG Stepped.zeroC
def prodRange [HasSize α] (N : α → ℕ) (M : QueryMachine Q A (α × ℕ) ℤ) : QueryMachine Q A α ℤ := foldRange N M Stepped.mulG Stepped.oneC
def gated [HasSize α] (M : QueryMachine Q A α Bool) (N : QueryMachine Q A α ℤ) : QueryMachine Q A α ℤ :=
  bind M (ite (fun p : α × Bool => p.2) (mapIn Prod.fst N) (const 0))
end QueryMachines.QueryMachine


