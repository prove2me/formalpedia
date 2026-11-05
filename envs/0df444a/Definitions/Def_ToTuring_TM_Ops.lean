-- Prove2me | Definitions.Def_ToTuring_TM_Ops
-- name    : ToTuring_TM_Ops
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:43:59.19802+00:00
-- url     : https://prove2.me/theorems/2ddcb1a8-1e41-4ff5-a4b1-401db1b4fe9f
-- title:
--   Ops
-- statement:
--   Definitions and structural lemmas for Ops, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Ops.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_TM_Move
import Theorems.Thm_Groundwork_TM_Frag_Within_seq

set_option autoImplicit false
section
section
namespace Groundwork.TM
open Turing
def pushSeq : List Sym → TM2.Stmt (fun _ : Stk => Sym) Empty (Option Sym)
  | [] => .halt
  | s :: w => .push .main (fun _ => s) (pushSeq w)
def pushW (w : List Sym) : Fr := Frag.ofStmt (pushSeq w.reverse)
def pop1 : Fr := Frag.ofStmt (.pop .main (fun _ _ => none) .halt)
def dropF : Fr := drp .main
def dupF : Fr := ((mv2 .main .a .b).seq (mv .a .main)).seq (mv .b .main)
def swapF : Fr := (((mv .main .a).seq (mv .main .b)).seq (mv .a .main)).seq (mv .b .main)
def consF : Fr :=
  (((((mv .main .a).seq (mv .main .b)).seq (pushW [.R])).seq (mv .b .main)).seq (mv .a .main)).seq (pushW [.L])
def unconsF : Fr :=
  (((((pop1).seq (mv .main .a)).seq (mv .main .b)).seq pop1).seq (mv .b .main)).seq (mv .a .main)
section
variable (x y : V) (M A B N : List Sym)
end
end Groundwork.TM


