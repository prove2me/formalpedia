-- Prove2me | Definitions.Def_CARDB_Asymptotics
-- name    : CARDB_Asymptotics
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T22:44:04.862868+00:00
-- url     : https://prove2.me/theorems/f62cfcc3-d6fe-571a-9dd2-6f6579771ff9
-- title:
--   Asymptotics
-- statement:
--   Definitions and structural lemmas for Asymptotics, from Lars Warren Ericson (catskillsresearch/cardb; see pinned Apache-2.0 LICENSE and NOTICE)'s pinned CARDB: The number of distinct topological bases of a finite set development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB/Asymptotics.lean

import Definitions.Def_CARDB
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
set_option autoImplicit true
open Set TopologicalSpace
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {x y : α}
noncomputable def packConstrained (a b : α) (hne : a ≠ b)
    (U : {U : Set α // a ∈ U → b ∈ U}) :
    Set {z : α // z ≠ a ∧ z ≠ b} × Fin 3 := by
  classical
  exact ({z | z.1 ∈ U.1},
    if a ∈ U.1 then ⟨2, by decide⟩ else if b ∈ U.1 then ⟨1, by decide⟩ else ⟨0, by decide⟩)
def specSet (t : TopologicalSpace α) : Set (α × α) :=
  {p | @Specializes α t p.1 p.2}
def specOffDiag (t : TopologicalSpace α) : Set {p : α × α // p.1 ≠ p.2} :=
  {p | @Specializes α t p.1.1 p.1.2}
open Filter Topology


