-- Prove2me | Definitions.Def_LeanFormalizations_Combinatorics_CombinatorialMap_EdgeInsertion
-- name    : LeanFormalizations_Combinatorics_CombinatorialMap_EdgeInsertion
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:45:21.279183+00:00
-- url     : https://prove2.me/theorems/bf44438f-e308-4250-a4b6-8b6eccc1e88e
-- title:
--   The cycle index set after splitting one cycle
-- statement:
--   For a permutation and a selected point, this defines a finite index set consisting of all other cycles together with two new positions. It provides the finite types needed to count this replacement.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_LeanFormalizations_Combinatorics_CombinatorialMap_Basic
import Mathlib
import Mathlib.GroupTheory.Perm.Cycle.Factors
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Sign

set_option autoImplicit true

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

open Equiv Equiv.Perm

namespace CombinatorialMap.EdgeInsertion

open scoped BigOperators

variable {α : Type*} [DecidableEq α] [Fintype α]


noncomputable instance instFintypeQuotientSameCycle (f : Perm α) :
    Fintype (Quotient (Equiv.Perm.SameCycle.setoid f)) :=
  Fintype.ofFinite _


abbrev SplitCyclePool (f : Perm α) (p : α) :=
  {r : Quotient (Equiv.Perm.SameCycle.setoid f) //
    r ≠ Quotient.mk (Equiv.Perm.SameCycle.setoid f) p} ⊕ Fin 2

noncomputable instance instFintypeSplitCyclePool (f : Perm α) (p : α) :
    Fintype (SplitCyclePool f p) := by
  classical
  infer_instance


section SumCongr

variable {β : Type*} [DecidableEq β] [Fintype β]


end SumCongr


section Construction

variable {D : Type*} [Fintype D] [DecidableEq D] (M : CombinatorialMap D) (c₁ c₂ : D)


end Construction


section LeafConstruction

variable {D : Type*} [Fintype D] [DecidableEq D] (M : CombinatorialMap D) (c : D)


end LeafConstruction


section Congr


variable {D D' : Type*} [Fintype D] [Fintype D'] [DecidableEq D] [DecidableEq D']
  {M : CombinatorialMap D} {M' : CombinatorialMap D'}


end Congr

end CombinatorialMap.EdgeInsertion


