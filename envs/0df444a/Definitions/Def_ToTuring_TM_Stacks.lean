-- Prove2me | Definitions.Def_ToTuring_TM_Stacks
-- name    : ToTuring_TM_Stacks
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:24:27.178794+00:00
-- url     : https://prove2.me/theorems/f758538a-a782-498d-8b5a-17651623257a
-- title:
--   Stacks
-- statement:
--   Definitions and structural lemmas for Stacks, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Stacks.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_TM_Frag
import Definitions.Def_ToTuring_TM_Tree
import Theorems.Thm_Groundwork_TM_beq_LR
import Theorems.Thm_Groundwork_TM_beq_RL
import Theorems.Thm_Groundwork_TM_beq_bL
import Theorems.Thm_Groundwork_TM_beq_bR
import Theorems.Thm_Groundwork_TM_length_mirror
attribute [local simp] Groundwork.TM.beq_LR
attribute [local simp] Groundwork.TM.beq_RL
attribute [local simp] Groundwork.TM.beq_bL
attribute [local simp] Groundwork.TM.beq_bR
attribute [local simp] Groundwork.TM.length_mirror


set_option autoImplicit false
section
section
namespace Groundwork.TM
open Turing
inductive Stk | main | a | b | cnt
  deriving DecidableEq
instance : Fintype Stk := ⟨{.main, .a, .b, .cnt}, fun x => by cases x <;> simp⟩
abbrev Fr := Frag (fun _ : Stk => Sym) (Option Sym)
def st (M A B N : List Sym) : Stk → List Sym
  | .main => M
  | .a => A
  | .b => B
  | .cnt => N
section
variable (M A B N W : List Sym)
end
end Groundwork.TM


