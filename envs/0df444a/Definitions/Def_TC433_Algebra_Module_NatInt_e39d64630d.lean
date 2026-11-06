-- Prove2me | Definitions.Def_TC433_Algebra_Module_NatInt_e39d64630d
-- name    : TC433_Algebra_Module_NatInt_e39d64630d
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T16:32:06.00008+00:00
-- url     : https://prove2.me/theorems/2ccc459e-d12c-4ecd-beb5-9c27050d0682
-- title:
--   TauCeti: Algebra / Module / NatInt
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.Algebra.Module.NatInt for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/Algebra/Module/NatInt.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Group.Action.Units
public import Mathlib.Algebra.Ring.Units

/-!
# Integer unit signs acting on modules

The sign action of an integer unit agrees with the action of its image in the scalar ring.
This lets integer signs in the scalar ring, such as powers of `-1`, combine with integer unit
actions.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

namespace TauCeti

/-- Acting by the image of an integer unit in the scalar ring and then by a second integer unit
is the action of their product as integer units. -/
theorem intCast_smul_units_smul {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
    (u' u : ℤˣ) (v : V) : ((u' : ℤ) : R) • u • v = (u' * u) • v := by
  rw [mul_smul, Units.smul_def u', ← Int.cast_smul_eq_zsmul R]

end TauCeti


