-- Prove2me | Definitions.Def_TC433_Algebra_Coalgebra_Cocommutative_9a65440ec2
-- name    : TC433_Algebra_Coalgebra_Cocommutative_9a65440ec2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:20:18.852197+00:00
-- url     : https://prove2.me/theorems/783d959a-10d3-4819-8efa-bc04e2a28e60
-- title:
--   TauCeti: Algebra / Coalgebra / Cocommutative
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.Algebra.Coalgebra.Cocommutative for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/Algebra/Coalgebra/Cocommutative.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Coalgebra.Hom

/-!
# Cocommutative coalgebras

Cocommutativity descends along surjective coalgebra homomorphisms. In particular, it
transfers across coalgebra equivalences without requiring compatible algebra structures.

## Main declarations

* `CoalgHom.isCocomm_of_surjective`: a surjective image of a cocommutative coalgebra is
  cocommutative.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

namespace CoalgHom

variable {R A B : Type*} [CommSemiring R] [AddCommMonoid A] [AddCommMonoid B]
  [Module R A] [Module R B] [Coalgebra R A] [Coalgebra R B]

/-- A surjective image of a cocommutative coalgebra is cocommutative. -/
theorem isCocomm_of_surjective (f : A →ₗc[R] B) (hf : Function.Surjective f)
    [hA : Coalgebra.IsCocomm R A] : Coalgebra.IsCocomm R B := by
  constructor
  ext b
  obtain ⟨a, rfl⟩ := hf b
  simpa only [CoalgHom.toLinearMap_eq_coe, CoalgHomClass.map_comp_comul_apply,
    Coalgebra.comm_comul, LinearMap.comp_apply, LinearEquiv.coe_coe] using
    (TensorProduct.map_comm f.toLinearMap f.toLinearMap (Coalgebra.comul a)).symm

end CoalgHom


