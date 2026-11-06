-- Prove2me | Definitions.Def_TC433_Algebra_Group_Subgroup_Centralizer_a410255429
-- name    : TC433_Algebra_Group_Subgroup_Centralizer_a410255429
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:15:29.226528+00:00
-- url     : https://prove2.me/theorems/7054821f-4b48-42e3-8de7-540aeca97e22
-- title:
--   TauCeti: Algebra / Group / Subgroup / Centralizer
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.Algebra.Group.Subgroup.Centralizer for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/Algebra/Group/Subgroup/Centralizer.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Subgroup.centralizer` occurs in the statement below.
public import Mathlib.GroupTheory.Subgroup.Centralizer
-- `Commute.units_val_iff` transports commutation between units and their values.
public import Mathlib.Algebra.Group.Commute.Units

/-!
# Centralizers and maximal commutative subgroups

Centralizers of a group of units are computed on the underlying monoid: a unit centralizes another
exactly when their values commute. Mathlib has both halves —
`Subgroup.mem_centralizer_singleton_iff` turns membership into an equation, and
`Commute.units_val_iff` transports that equation between `Mˣ` and `M` — but not their combination,
which is the form every concrete centralizer computation in a matrix group starts from.

## Main results

* `TauCeti.mem_centralizer_singleton_iff_commute_val`: a unit lies in the centralizer of a unit `g`
  exactly when the two commute as elements of the monoid.
* `Subgroup.eq_of_centralizer_eq_self_of_le_of_isMulCommutative`: a self-centralizing subgroup is
  maximal among commutative subgroups.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

namespace TauCeti

/-- Membership in the centralizer of a unit `g`, read on the underlying monoid. -/
theorem mem_centralizer_singleton_iff_commute_val {M : Type*} [Monoid M] {g h : Mˣ} :
    h ∈ Subgroup.centralizer {g} ↔ Commute (g : M) (h : M) :=
  ⟨fun hh => Commute.units_val_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp hh).symm,
    fun hh => Subgroup.mem_centralizer_singleton_iff.mpr (Commute.units_val_iff.mp hh).symm⟩

end TauCeti

namespace Subgroup

/-- A self-centralizing subgroup is maximal among commutative subgroups. -/
theorem eq_of_centralizer_eq_self_of_le_of_isMulCommutative {G : Type*} [Group G]
    {S H : Subgroup G} (hS : Subgroup.centralizer (S : Set G) = S) [IsMulCommutative H]
    (hle : S ≤ H) :
    H = S :=
  le_antisymm
    (by
      rw [← hS]
      exact (Subgroup.le_centralizer (H := H)).trans
        (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hle)))
    hle

end Subgroup


