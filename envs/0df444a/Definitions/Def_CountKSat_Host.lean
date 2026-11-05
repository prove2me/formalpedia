-- Prove2me | Definitions.Def_CountKSat_Host
-- name    : CountKSat_Host
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:46:19.19649+00:00
-- url     : https://prove2.me/theorems/a969e841-374d-4904-91b5-06ee1b0798a8
-- title:
--   Host
-- statement:
--   Definitions and structural lemmas for Host, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Host.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_ToTuring_Machine_Host
import Theorems.Thm_Groundwork_TM_Frag_Within_seq

set_option autoImplicit false
section
namespace CountKSat.HostW
open Groundwork Groundwork.TM Groundwork.Host Turing
def chkW : TM2.Stmt Γio Unit (Option Sym) :=
  .pop (some .main) (fun _ _ => none) <| .peek (some .main) (fun _ o => o) <|
    .branch (fun s => s == some .R)
      (.pop (some .main) (fun _ _ => none) <| .goto fun _ => ())
      (.load (fun _ => none) .halt)
def unpackQ : TM2.Stmt Γio Unit (Option Sym) :=
  .pop (some .main) (fun _ _ => none) <| .pop (some .main) (fun _ o => o) <|
    .branch (fun s => s == some .R)
      (.load (fun _ => none) .halt)
      (.push (some .a) (fun s => s.getD .L) <| .load (fun _ => none) <| .goto fun _ => ())
def unpack : FrIO := Frag.loop unpackQ skip
def emitQ : TM2.Stmt Γio Unit (Option Sym) :=
  .pop (some .a) (fun _ o => o) <|
    .branch (fun s => s.isSome)
      (.push none bitOf <| .pop (some .main) (fun _ _ => none) <| .goto fun _ => ())
      .halt
def emit : FrIO := Frag.loop emitQ skip
section
variable (W : List Bool) (M A B N : List Sym)
end
def pop3 : FrIO := Frag.ofStmt (.pop (some .main) (fun _ _ => none) <| .pop (some .main) (fun _ _ => none) <|
  .pop (some .main) (fun _ _ => none) .halt)
def epilogue : FrIO := (unpack.seq emit).seq pop3
section machine
variable {M : Stepped (List Bool) (List Bool)}
variable [Enc M.σ]
def mainLoop (Ps Po : Fr) : FrIO := Frag.loop chkW (body Ps Po)
variable {Ps Po : Fr} {tS tO : ℕ → ℕ}
  (hS : ∀ (s : M.σ) (M' A B N : List Sym),
    Ps.Within (st (wd s ++ M') A B N) (tS (len s)) (st (wd (M.step s) ++ M') A B N))
  (hO : ∀ (s : M.σ) (M' A B N : List Sym),
    Po.Within (st (wd s ++ M') A B N) (tO (len s)) (st (wd (M.out s) ++ M') A B N))
end machine
def prog (Pi Ps Po : Fr) : FrIO :=
  (((prologue.seq (Pi.seq (look Po)).io).seq (mainLoop Ps Po)).seq epilogue).seq dropF.io
end CountKSat.HostW
namespace CountKSat
open Groundwork Groundwork.TM Groundwork.Host Turing HostW
end CountKSat


