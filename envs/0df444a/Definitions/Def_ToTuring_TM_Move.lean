-- Prove2me | Definitions.Def_ToTuring_TM_Move
-- name    : ToTuring_TM_Move
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:29:23.986106+00:00
-- url     : https://prove2.me/theorems/a3ef3b57-86c3-43f0-935f-5f4daa41b762
-- title:
--   Move
-- statement:
--   Definitions and structural lemmas for Move, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Move.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_TM_Rename
import Definitions.Def_ToTuring_TM_Stacks
import Theorems.Thm_Groundwork_TM_beq_LR
import Theorems.Thm_Groundwork_TM_beq_RL
import Theorems.Thm_Groundwork_TM_beq_bL
import Theorems.Thm_Groundwork_TM_beq_bR
import Theorems.Thm_Groundwork_TM_length_mirror
import Theorems.Thm_Groundwork_TM_st_a
import Theorems.Thm_Groundwork_TM_st_b
import Theorems.Thm_Groundwork_TM_st_cnt
import Theorems.Thm_Groundwork_TM_st_main
import Theorems.Thm_Groundwork_TM_upd_a
import Theorems.Thm_Groundwork_TM_upd_b
import Theorems.Thm_Groundwork_TM_upd_main
attribute [local simp] Groundwork.TM.beq_LR
attribute [local simp] Groundwork.TM.beq_RL
attribute [local simp] Groundwork.TM.beq_bL
attribute [local simp] Groundwork.TM.beq_bR
attribute [local simp] Groundwork.TM.length_mirror
attribute [local simp] Groundwork.TM.st_a
attribute [local simp] Groundwork.TM.st_b
attribute [local simp] Groundwork.TM.st_cnt
attribute [local simp] Groundwork.TM.st_main
attribute [local simp] Groundwork.TM.upd_a
attribute [local simp] Groundwork.TM.upd_b
attribute [local simp] Groundwork.TM.upd_main


set_option autoImplicit false
section
section
namespace Groundwork.TM
open Turing
inductive S4 | src | t1 | t2 | cnt
  deriving DecidableEq
inductive MvL | start | loop
  deriving DecidableEq
instance : Fintype MvL := ⟨{.start, .loop}, fun x => by cases x <;> simp⟩
abbrev St4 := TM2.Stmt (fun _ : S4 => Sym) MvL (Option Sym)
def pushIf (p : Bool) (k : S4) (f : Option Sym → Sym) (q : St4) : St4 := if p then .push k f q else q
def mvChk : St4 :=
  .peek .cnt (fun _ o => o) <|
    .branch (fun s => s == some .L) (.pop .cnt (fun _ _ => none) .halt) (.load (fun _ => none) <| .goto fun _ => .loop)
def mvM (p₁ p₂ : Bool) : MvL → St4
  | .start => .push .cnt (fun _ => .L) <| .goto fun _ => .loop
  | .loop => .pop .src (fun _ o => o) <|
      .branch (fun s => s == some .L)
        (pushIf p₁ .t1 (fun _ => .R) <| pushIf p₂ .t2 (fun _ => .R) <| .push .cnt (fun _ => .R) <|
          .load (fun _ => none) <| .goto fun _ => .loop)
        (.branch (fun s => s == some .R)
          (pushIf p₁ .t1 (fun _ => .L) <| pushIf p₂ .t2 (fun _ => .L) <| .pop .cnt (fun s _ => s) mvChk)
          (pushIf p₁ .t1 (fun s => s.getD .L) <| pushIf p₂ .t2 (fun s => s.getD .L) mvChk))
def mvB (p₁ p₂ : Bool) : Frag (fun _ : S4 => Sym) (Option Sym) := ⟨MvL, .start, mvM p₁ p₂⟩
def toStk (i j k : Stk) : S4 → Stk
  | .src => i
  | .t1 => j
  | .t2 => k
  | .cnt => .cnt
def other (i j : Stk) : Stk :=
  if i ≠ .main ∧ j ≠ .main then .main else if i ≠ .a ∧ j ≠ .a then .a else .b
def mv (i j : Stk) : Fr := (mvB true false).ren (toStk i j (other i j))
def mv2 (i j k : Stk) : Fr := (mvB true true).ren (toStk i j k)
def drp (i : Stk) : Fr := (mvB false false).ren (toStk i (other i i) (other i (other i i)))
def st4 (A B₁ B₂ C : List Sym) : S4 → List Sym
  | .src => A
  | .t1 => B₁
  | .t2 => B₂
  | .cnt => C
section
variable (A B₁ B₂ C W : List Sym)
end
def putIf (p : Bool) (w B : List Sym) : List Sym := if p then w ++ B else B
section steps
variable (p₁ p₂ : Bool) (A B₁ B₂ C : List Sym)
end steps
end Groundwork.TM


