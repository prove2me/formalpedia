-- Prove2me | Definitions.Def_VariableBound_Search_Correct
-- name    : VariableBound_Search_Correct
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:50:36.071384+00:00
-- url     : https://prove2.me/theorems/61eb7f33-9c72-41af-8783-95715ca4fabf
-- title:
--   Correct
-- statement:
--   Definitions and structural lemmas for Correct, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Search/Correct.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Search_Defs
import Definitions.Def_VariableBound_StepChoice
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
@[expose] section
namespace VariableBound.Search
open Groundwork PaddedDescent.F AppVariables Finset
@[expose] def den (nb β rb tb r : ℕ) : ℚ := 3 ^ r * 2 ^ (β - 1) * 2 ^ tb * (15 * nb) ^ (rb - r)
@[expose] def stepD (key : List ℕ → ℤ) (best : Option (List ℕ × ℤ)) (l : List ℕ) : Option (List ℕ × ℤ) :=
  best.elim (some (l, key l)) fun b => if key l < b.2 then some (l, key l) else some b
section Loop
variable {X : Type} [Fintype X] {m : ℕ} (V : X → Finset (Fin m)) (n nb rb tb : ℕ) (fam : List (List ℕ))
@[expose] def Inv (L : List (List ℕ)) : Prop :=
  (∀ l ∈ L, l ∈ fam) ∧ Reached V nb (beta n m nb) rb tb (univ : Finset (Fin fam.length)) (fun i => Fld.setD m (fam.get i)) (chksD m L)
structure Hyp (X : Type) [Fintype X] (m n nb rb tb : ℕ) (fam : List (List ℕ)) : Prop where
  hX : Fintype.card X ≤ 2 ^ n
  hnb : 1 ≤ nb
  hrb : IsRb (beta n m nb) rb
  htb : IsTb m nb rb tb
  hne : fam ≠ []
  hinc : ∀ l ∈ fam, l.Pairwise (· < ·) ∧ ∀ E ∈ l, E < m
  hF : IsFamily nb (univ : Finset (Fin fam.length)) (fun i => Fld.setD m (fam.get i))
variable {V n nb rb tb fam}
end Loop
end VariableBound.Search
namespace VariableBound
open Groundwork PaddedDescent.F AppVariables Finset
end VariableBound


