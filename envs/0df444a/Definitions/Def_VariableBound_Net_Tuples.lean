-- Prove2me | Definitions.Def_VariableBound_Net_Tuples
-- name    : VariableBound_Net_Tuples
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:05:04.391263+00:00
-- url     : https://prove2.me/theorems/083210a5-e06d-48b3-ae50-e49d8ac80c15
-- title:
--   Tuples
-- statement:
--   Definitions and structural lemmas for Tuples, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tuples.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_VariableBound_Net_Basic
import Mathlib.Tactic.Convert
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.GetD
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
namespace VariableBound.Net.Tuples
open Groundwork Groundwork.Prog Finset PaddedDescent.F VariableBound.Net.Basic
open PaddedDescent.F.Mark (Cl qv vio WfL occ)
open ClauseBound.ParityChecks (Vof)
variable {k n : ℕ} {D : Dat}
open Classical in
/-- The clauses E such that the object (κ, E, j) is a member of P: Π₀ for (κ, j) = (0, 0), Π_j for κ = 1. -/
noncomputable def sl (D : Dat) (κ j : ℕ) (P : Finset ℕ) : Finset (Fin D.1.length) := univ.filter fun e => ∃ o ∈ P, obAt D o = (κ, e.val, j)
open Classical in
/-- The set of the objects E with E ∈ S₀ and (E, j) with E ∈ S j. -/
noncomputable def back (D : Dat) {r : ℕ} (S₀ : Finset (Fin D.1.length)) (S : Fin r → Finset (Fin D.1.length)) : Finset ℕ :=
  (range (objs D).length).filter fun o => (∃ e ∈ S₀, obAt D o = (0, e.val, 0)) ∨ ∃ j, ∃ e ∈ S j, obAt D o = (1, e.val, j.val)
end VariableBound.Net.Tuples


