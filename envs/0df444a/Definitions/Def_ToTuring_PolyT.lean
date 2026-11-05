-- Prove2me | Definitions.Def_ToTuring_PolyT
-- name    : ToTuring_PolyT
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:44:39.420934+00:00
-- url     : https://prove2.me/theorems/bca8aa70-de82-478f-93e4-fe3fc85ea2f0
-- title:
--   Poly T
-- statement:
--   Definitions and structural lemmas for Poly T, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/PolyT.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Enc
import Definitions.Def_ToTuring_TM_Ops
import Definitions.Def_ToTuring_Bound
import Mathlib.Tactic.FunProp
set_option autoImplicit false
section
section
namespace Groundwork
open TM
@[fun_prop] def PolyT {α β : Type} [Enc α] [Enc β] (f : α → β) : Prop :=
  ∃ (P : Fr) (c : ℕ),
    (∀ (x : α) (M A B N : List Sym), ∃ n ≤ c * (len x + 1) ^ c,
      P.Runs none (st (wd x ++ M) A B N) n (st (wd (f x) ++ M) A B N)) ∧
    ∀ x, len (f x) ≤ c * (len x + 1) ^ c
def Unary {α : Type} [Enc α] (f : α → ℕ) : Prop := PolyT fun x => List.replicate (f x) ()
class IsPolyT {α β : Type} [Enc α] [Enc β] (M : Stepped α β) where
  [enc : Enc M.σ]
  [carried : Carried M.σ]
  init : PolyT M.init
  step : PolyT M.step
  out : PolyT M.out
instance {α β : Type} [Enc α] [Enc β] (M : Stepped α β) [h : IsPolyT M] : Enc M.σ := h.enc
instance {α β : Type} [Enc α] [Enc β] (M : Stepped α β) [h : IsPolyT M] : Carried M.σ := h.carried
end Groundwork


