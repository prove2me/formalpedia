-- Prove2me | Definitions.Def_ToTuring_TM_Tree
-- name    : ToTuring_TM_Tree
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:20:51.213238+00:00
-- url     : https://prove2.me/theorems/4c429518-d0ac-4158-983f-959c62a23f4f
-- title:
--   Tree
-- statement:
--   Definitions and structural lemmas for Tree, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Tree.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
set_option autoImplicit false
section
section
namespace Groundwork.TM
inductive Sym | bit (b : Bool) | L | R
  deriving DecidableEq
instance : Fintype Sym := ⟨{.bit false, .bit true, .L, .R}, fun x => by rcases x with (_ | _) | _ | _ <;> simp⟩
inductive V | nil | bit (b : Bool) | cons (x y : V)
def code : V → List Sym
  | .nil => [.L, .R]
  | .bit b => [.bit b]
  | .cons x y => .L :: (code x ++ code y ++ [.R])
def Sym.flip : Sym → Sym
  | .L => .R
  | .R => .L
  | s => s
def mirror (w : List Sym) : List Sym := (w.map Sym.flip).reverse
def V.mir : V → V
  | .nil => .nil
  | .bit b => .bit b
  | .cons x y => .cons y.mir x.mir
end Groundwork.TM


