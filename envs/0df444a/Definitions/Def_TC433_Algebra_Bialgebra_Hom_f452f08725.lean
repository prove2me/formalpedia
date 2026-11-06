-- Prove2me | Definitions.Def_TC433_Algebra_Bialgebra_Hom_f452f08725
-- name    : TC433_Algebra_Bialgebra_Hom_f452f08725
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T10:16:02.131611+00:00
-- url     : https://prove2.me/theorems/2373b023-fdbe-4dd0-8bbe-7be88ec0ad9f
-- title:
--   TauCeti: Algebra / Bialgebra / Hom
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.Algebra.Bialgebra.Hom for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/Algebra/Bialgebra/Hom.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.Hom

/-!
# Ring homomorphisms underlying bialgebra morphisms

`BialgHom.id_toRingHom` identifies the direct ring-homomorphism coercion of the identity.
It complements Mathlib's `BialgHom.id_toAlgHom`, which concerns the algebra-homomorphism
coercion.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

namespace BialgHom

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] [CoalgebraStruct R A]

/-- The ring homomorphism underlying the identity bialgebra morphism is the identity. -/
@[simp]
theorem id_toRingHom : (BialgHom.id R A : A →+* A) = RingHom.id A := rfl

end BialgHom


