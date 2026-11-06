-- Prove2me | Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_ReeF4_Closure_157552f9bf
-- name    : TC433_GroupTheory_SpecificGroups_CFSG_ReeF4_Closure_157552f9bf
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:16:19.834356+00:00
-- url     : https://prove2.me/theorems/fcee95f5-c94b-422a-8d61-c39e9851f1e9
-- title:
--   TauCeti: GroupTheory / SpecificGroups / CFSG / ReeF4 / Closure
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.GroupTheory.SpecificGroups.CFSG.ReeF4.Closure for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/GroupTheory/SpecificGroups/CFSG/ReeF4/Closure.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.ZMod
public import Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_Closure_ec99479228
public import Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_ReeF4_Index_9ac91658a8

/-!
# The algebraic closure for the Ree family of type `F₄`

This file records that the algebraic closure attached to a validated Ree index of type `F₄` has
characteristic two, and equips it with the resulting structure of an algebra over the field of two
elements. That is the form in which the characteristic reaches a construction on the family's
carrier, whose defining equations live in characteristic two and whose base ring is `ZMod 2`
itself.

## Main results

* `TauCeti.ReeF4LieIndex.charP_closure_two`: the algebraic closure attached to a Ree index of
  type `F₄` has characteristic two.
* `TauCeti.ReeF4LieIndex.algebraZModTwo`: the resulting `ZMod 2`-algebra structure on it.
-/

-- Adapted from `TauCeti.GroupTheory.SpecificGroups.CFSG.ReeG2.Closure`.

public section
set_option backward.isDefEq.respectTransparency.types false

namespace TauCeti.ReeF4LieIndex

/-- The algebraic closure attached to a Ree index of type `F₄` has characteristic two. -/
instance charP_closure_two (d : ReeF4LieIndex) : CharP d.1.Closure 2 := by
  rw [← d.characteristic_eq_two]
  infer_instance

/-- The algebraic closure attached to a Ree index of type `F₄` is an algebra over the field of two
elements, this being the base ring over which its carrier is defined. Characteristic two forces
the structure: any two `ZMod 2`-algebra structures on a ring agree. -/
noncomputable instance algebraZModTwo (d : ReeF4LieIndex) : Algebra (ZMod 2) d.1.Closure :=
  ZMod.algebra d.1.Closure 2

end TauCeti.ReeF4LieIndex


