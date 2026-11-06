-- Prove2me | Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_Tits_Closure_56eff4b204
-- name    : TC433_GroupTheory_SpecificGroups_CFSG_Tits_Closure_56eff4b204
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:16:59.016277+00:00
-- url     : https://prove2.me/theorems/1dd55ac4-276f-4508-a525-bdbbe3a7a48a
-- title:
--   TauCeti: GroupTheory / SpecificGroups / CFSG / Tits / Closure
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.GroupTheory.SpecificGroups.CFSG.Tits.Closure for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/GroupTheory/SpecificGroups/CFSG/Tits/Closure.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.ZMod
public import Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_Closure_ec99479228
public import Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_Tits_Index_756db47e3f

/-!
# The algebraic closure for the Tits construction

This file records that the algebraic closure attached to the validated Tits index has
characteristic two, and equips it with the resulting structure of an algebra over the field of two
elements. These are the structures through which the index reaches the explicit type-`F₄` carrier
and its exceptional isogeny.

## Main results

* `TauCeti.TitsLieIndex.charP_closure_two`: the algebraic closure attached to the Tits index has
  characteristic two.
* `TauCeti.TitsLieIndex.algebraZModTwo`: the resulting `ZMod 2`-algebra structure.
-/

-- Adapted from `TauCeti.GroupTheory.SpecificGroups.CFSG.ReeG2.Closure`.

public section
set_option backward.isDefEq.respectTransparency.types false

namespace TauCeti.TitsLieIndex

/-- The algebraic closure attached to the Tits index has characteristic two. -/
instance charP_closure_two (d : TitsLieIndex) : CharP d.1.Closure 2 := by
  rw [← d.characteristic_eq_two]
  infer_instance

/-- The algebraic closure attached to the Tits index is an algebra over the field of two elements,
the base ring over which its short-root carrier is defined. -/
noncomputable instance algebraZModTwo (d : TitsLieIndex) : Algebra (ZMod 2) d.1.Closure :=
  ZMod.algebra d.1.Closure 2

end TauCeti.TitsLieIndex


