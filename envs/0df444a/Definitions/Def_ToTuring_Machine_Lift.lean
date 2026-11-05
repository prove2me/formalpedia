-- Prove2me | Definitions.Def_ToTuring_Machine_Lift
-- name    : ToTuring_Machine_Lift
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:26:15.999466+00:00
-- url     : https://prove2.me/theorems/5d7a1370-cb87-404d-9824-3ab184e606ce
-- title:
--   Lift
-- statement:
--   Definitions and structural lemmas for Lift, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/Lift.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_TM_Stacks
set_option autoImplicit false
section
section
namespace Groundwork.TM
open Turing
abbrev Γio : Option Stk → Type
  | none => Bool
  | some _ => Sym
def liftIO {Λ σ : Type} : TM2.Stmt (fun _ : Stk => Sym) Λ σ → TM2.Stmt Γio Λ σ
  | .push k f q => .push (some k) f (liftIO q)
  | .peek k f q => .peek (some k) f (liftIO q)
  | .pop k f q => .pop (some k) f (liftIO q)
  | .load f q => .load f (liftIO q)
  | .branch p q₁ q₂ => .branch p (liftIO q₁) (liftIO q₂)
  | .goto l => .goto l
  | .halt => .halt
def Frag.io (P : Fr) : Frag Γio (Option Sym) where
  Λ := P.Λ
  entry := P.entry
  m l := liftIO (P.m l)
def withIO (W : List Bool) (S : Stk → List Sym) : ∀ k, List (Γio k)
  | none => W
  | some k => S k
def liftCfg {Λ σ : Type} (W : List Bool) (c : TM2.Cfg (fun _ : Stk => Sym) Λ σ) : TM2.Cfg Γio Λ σ := ⟨c.l, c.var, withIO W c.stk⟩
end Groundwork.TM


