-- Prove2me | Definitions.Def_ToTuring_Machine_Host
-- name    : ToTuring_Machine_Host
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:45:34.342552+00:00
-- url     : https://prove2.me/theorems/3b62bba7-dad4-4e8f-bd31-03ec040850b5
-- title:
--   Host
-- statement:
--   Definitions and structural lemmas for Host, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/Host.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Machine_Lift
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_EncLemmas
import Theorems.Thm_Groundwork_TM_Frag_Within_seq

set_option autoImplicit false
section
section
namespace Groundwork
open TM Turing
namespace Host
abbrev FrIO := Frag Γio (Option Sym)
def skip : FrIO := Frag.ofStmt .halt
def pourQ : TM2.Stmt Γio Unit (Option Sym) :=
  .pop none (fun _ o => o.map Sym.bit) <|
    .branch (fun s => s.isSome)
      (.push (some .a) (fun s => s.getD .L) <| .push (some .main) (fun _ => .R) <| .load (fun _ => none) <|
        .goto fun _ => ())
      .halt
def pour : FrIO := Frag.loop pourQ skip
def buildQ : TM2.Stmt Γio Unit (Option Sym) :=
  .pop (some .a) (fun _ o => o) <|
    .branch (fun s => s.isSome)
      (.push (some .main) (fun s => s.getD .L) <| .push (some .main) (fun _ => .L) <| .load (fun _ => none) <|
        .goto fun _ => ())
      .halt
def build : FrIO := Frag.loop buildQ skip
section
variable (W : List Bool) (M A B N : List Sym)
end
def prologue : FrIO := (pour.seq (pushW [.L, .R]).io).seq build
def bitOf : Option Sym → Bool
  | some (.bit b) => b
  | _ => false
def chkQ : TM2.Stmt Γio Unit (Option Sym) :=
  .pop (some .main) (fun _ _ => none) <| .pop (some .main) (fun _ o => o) <|
    .branch (fun s => s == some .R)
      (.load (fun _ => none) <| .goto fun _ => ())
      (.push none bitOf <| .pop (some .main) (fun _ _ => none) <| .pop (some .main) (fun _ _ => none) <|
        .pop (some .main) (fun _ _ => none) .halt)
section
variable (W : List Bool) (M A B N : List Sym)
end
section machine
variable {M : Stepped (List Bool) Bool}
variable [Enc M.σ]
def look (Po : Fr) : Fr := dupF.seq Po
def body (Ps Po : Fr) : FrIO := (Ps.seq (look Po)).io
def mainLoop (Ps Po : Fr) : FrIO := Frag.loop chkQ (body Ps Po)
variable {Ps Po : Fr} {tS tO : ℕ → ℕ}
  (hS : ∀ (s : M.σ) (M' A B N : List Sym),
    Ps.Within (st (wd s ++ M') A B N) (tS (len s)) (st (wd (M.step s) ++ M') A B N))
  (hO : ∀ (s : M.σ) (M' A B N : List Sym),
    Po.Within (st (wd s ++ M') A B N) (tO (len s)) (st (wd (M.out s) ++ M') A B N))
end machine
def prog (Pi Ps Po : Fr) : FrIO := ((prologue.seq (Pi.seq (look Po)).io).seq (mainLoop Ps Po)).seq dropF.io
def tmOf (H : FrIO) : FinTM2 where
  K := Option Stk
  k₀ := none
  k₁ := none
  Γ := Γio
  Λ := H.Λ
  main := H.entry
  σ := Option Sym
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := H.m
end Host
end Groundwork


