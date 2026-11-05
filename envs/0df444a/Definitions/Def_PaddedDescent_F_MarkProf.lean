-- Prove2me | Definitions.Def_PaddedDescent_F_MarkProf
-- name    : PaddedDescent_F_MarkProf
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:07:59.349245+00:00
-- url     : https://prove2.me/theorems/506156a2-2913-4418-b752-30a5eb4350af
-- title:
--   Mark Prof
-- statement:
--   Definitions and structural lemmas for Mark Prof, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkProf.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_StepMachines_Math_Digits
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
@[expose] section
namespace PaddedDescent.F.Mark.Prof
open Groundwork Groundwork.Prog Groundwork.Grid Finset
def tset (g n : ℕ) (Ls : List Fml) (e : ℕ) : Finset ℕ := (range g).filter fun a => tchB g n Ls a e = true
def tgt (g n : ℕ) (Ls : List Fml) (P : Finset ℕ) (q : ℕ) : ℕ :=
  if q / Ls.length % g < q / Ls.length / g then 0
  else if q / Ls.length / g = q / Ls.length % g then oc g n Ls P (q / Ls.length / g) (q % Ls.length)
  else pw g n Ls P (q / Ls.length / g) (q / Ls.length % g) (q % Ls.length)
end PaddedDescent.F.Mark.Prof


