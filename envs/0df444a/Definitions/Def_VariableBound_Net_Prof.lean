-- Prove2me | Definitions.Def_VariableBound_Net_Prof
-- name    : VariableBound_Net_Prof
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:05:23.422948+00:00
-- url     : https://prove2.me/theorems/3cf98c4b-89c6-4c73-b85f-1c8bb61a3d88
-- title:
--   Prof
-- statement:
--   Definitions and structural lemmas for Prof, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Prof.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Basic
import Definitions.Def_StepMachines_Math_Digits
import Definitions.Def_PaddedDescent_F_MarkProf
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Groundwork_PolyT_filter
attribute [local fun_prop] Groundwork.PolyT.filter


set_option autoImplicit false
section
section
@[expose] section
namespace VariableBound.Net.Prof
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F Finset
open PaddedDescent.F.Mark (Cl qv vio WfL occ nProf)
def tset (g n : ℕ) (D : Dat) (o : ℕ) : Finset ℕ := (range g).filter fun a => tchB g n D a o = true
def tgt (g n : ℕ) (D : Dat) (P : Finset ℕ) (q : ℕ) : ℕ :=
  if q / 2 % g < q / 2 / g then 0
  else if q / 2 / g = q / 2 % g then oc g n D P (q / 2 / g) (q % 2)
  else pw g n D P (q / 2 / g) (q / 2 % g) (q % 2)
end VariableBound.Net.Prof


