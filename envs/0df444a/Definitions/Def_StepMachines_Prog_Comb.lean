-- Prove2me | Definitions.Def_StepMachines_Prog_Comb
-- name    : StepMachines_Prog_Comb
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:20:28.690206+00:00
-- url     : https://prove2.me/theorems/df525d96-119d-482d-8d0e-34c514a23875
-- title:
--   Comb
-- statement:
--   Definitions and structural lemmas for Comb, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Comb.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
set_option autoImplicit false
section
namespace Groundwork.Stepped
variable {α α₁ α₂ β γ δ ι : Type}
@[expose] public def branch (sel : α → α₁ ⊕ α₂) (M₁ : Stepped α₁ β) (M₂ : Stepped α₂ β) : Stepped α β where
  σ := M₁.σ ⊕ M₂.σ
  init a := match sel a with | .inl x => .inl (M₁.init x) | .inr y => .inr (M₂.init y)
  step s := match s with | .inl s => .inl (M₁.step s) | .inr s => .inr (M₂.step s)
  out s := match s with | .inl s => M₁.out s | .inr s => M₂.out s
@[expose] public def iteSel (p : α → Bool) (a : α) : α ⊕ α := if p a then .inl a else .inr a
@[expose] public def ite (p : α → Bool) (M N : Stepped α β) : Stepped α β := branch (iteSel p) M N
@[expose] public def const [HasSize α] [HasSize β] (b : β) : Stepped α β := ofFun (Function.const α b)
@[expose] public def optSel (x : α × Option ι) : (α × ι) ⊕ α :=
  match x.2 with | some i => .inl (x.1, i) | none => .inr x.1
@[expose] public def optBind [HasSize α] [HasSize β] (M : Stepped α (Option ι)) (N : Stepped (α × ι) β)
    (dflt : α → β) : Stepped α β :=
  bind M (branch optSel N (ofFun dflt))
@[expose] public def both [HasSize α] [HasSize β] (M : Stepped α β) (N : Stepped α γ) : Stepped α (β × γ) where
  σ := (α × M.σ) ⊕ (β × N.σ)
  init a := .inl (a, M.init a)
  step s := match s with
    | .inl p => match M.out p.2 with
      | some b => .inr (b, N.init p.1)
      | none => .inl (p.1, M.step p.2)
    | .inr p => .inr (p.1, N.step p.2)
  out s := match s with | .inl _ => none | .inr p => (N.out p.2).map fun c => (p.1, c)
@[expose] public def map2 [HasSize α] [HasSize β] (f : β → γ → δ) (M : Stepped α β) (N : Stepped α γ) :
    Stepped α δ :=
  mapOut (both M N) (Function.uncurry f)
@[expose] public def mul2 [HasSize α] (M N : Stepped α ℤ) : Stepped α ℤ := map2 Int.mul M N
end Groundwork.Stepped


