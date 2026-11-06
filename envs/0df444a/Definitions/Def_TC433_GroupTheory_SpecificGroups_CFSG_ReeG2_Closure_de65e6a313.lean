-- Prove2me | Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_ReeG2_Closure_de65e6a313
-- name    : TC433_GroupTheory_SpecificGroups_CFSG_ReeG2_Closure_de65e6a313
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:16:52.436547+00:00
-- url     : https://prove2.me/theorems/03463092-8e0e-4c00-bbae-8660e542a6af
-- title:
--   TauCeti: GroupTheory / SpecificGroups / CFSG / ReeG2 / Closure
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.GroupTheory.SpecificGroups.CFSG.ReeG2.Closure for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/GroupTheory/SpecificGroups/CFSG/ReeG2/Closure.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.ZMod
public import Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_Closure_ec99479228
public import Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_ReeG2_Index_bc118784a9

/-!
# The algebraic closure for the Ree family of type `G₂`

This file records that the algebraic closure attached to a validated Ree index of type `G₂` has
characteristic three, and equips it with the resulting structure of an algebra over the field of
three elements. This is the base ring over which the family's short-root carrier is defined.

## Main results

* `TauCeti.ReeG2LieIndex.charP_closure_three`: the algebraic closure attached to a Ree index of
  type `G₂` has characteristic three.
* `TauCeti.ReeG2LieIndex.algebraZModThree`: the resulting `ZMod 3`-algebra structure on it.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

namespace TauCeti.ReeG2LieIndex

/-- The algebraic closure attached to a Ree index of type `G₂` has characteristic three. -/
instance charP_closure_three (d : ReeG2LieIndex) : CharP d.1.Closure 3 := by
  rw [← d.characteristic_eq_three]
  infer_instance

/-- The algebraic closure attached to a Ree index of type `G₂` is an algebra over the field of
three elements, the base ring of the family's carrier. Characteristic three determines this
structure uniquely. -/
noncomputable instance algebraZModThree (d : ReeG2LieIndex) : Algebra (ZMod 3) d.1.Closure :=
  ZMod.algebra d.1.Closure 3

end TauCeti.ReeG2LieIndex


