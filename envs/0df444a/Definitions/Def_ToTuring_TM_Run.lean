-- Prove2me | Definitions.Def_ToTuring_TM_Run
-- name    : ToTuring_TM_Run
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:16:25.152169+00:00
-- url     : https://prove2.me/theorems/b6b8757b-419c-4f32-acb9-f2702bb0ca61
-- title:
--   Run
-- statement:
--   Definitions and structural lemmas for Run, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Run.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Computability.TuringMachine.Computable
set_option autoImplicit false
section
section
namespace Groundwork.TM
open Turing
def Run {C : Type} (f : C → Option C) : C → ℕ → C → Prop
  | a, 0, b => a = b
  | a, n + 1, b => ∃ c, f a = some c ∧ Run f c n b
variable {K : Type} [DecidableEq K] {Γ : K → Type} {σ : Type}
section place
variable {Λ Λ' : Type} (ι : Λ → Λ') (e : Option Λ')
def place : TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ' σ
  | .push k f q => .push k f (place q)
  | .peek k f q => .peek k f (place q)
  | .pop k f q => .pop k f (place q)
  | .load f q => .load f (place q)
  | .branch p q₁ q₂ => .branch p (place q₁) (place q₂)
  | .goto l => .goto (ι ∘ l)
  | .halt => match e with
    | some e => .goto fun _ => e
    | none => .halt
def placeCfg (c : TM2.Cfg Γ Λ σ) : TM2.Cfg Γ Λ' σ := ⟨c.l.elim e (some ∘ ι), c.var, c.stk⟩
end place
end Groundwork.TM


