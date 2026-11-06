-- Prove2me | Definitions.Def_TC433_Algebra_AlgebraicGroup_Tangent_FiniteType_a70fd31556
-- name    : TC433_Algebra_AlgebraicGroup_Tangent_FiniteType_a70fd31556
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:22:03.714081+00:00
-- url     : https://prove2.me/theorems/09eafd57-4d66-4249-b14e-6187216fb222
-- title:
--   TauCeti: Algebra / AlgebraicGroup / Tangent / FiniteType
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.Algebra.AlgebraicGroup.Tangent.FiniteType for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/Algebra/AlgebraicGroup/Tangent/FiniteType.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FiniteType
public import Definitions.Def_TC433_Algebra_AlgebraicGroup_Tangent_Cotangent_2534c94ce5
public import Definitions.Def_TC433_RingTheory_Ideal_Cotangent_Basic_8c7f6183b5

/-!
# Finiteness of the tangent space of a finite-type affine monoid

The counit of a commutative bialgebra of finite type over a noetherian base has finite cotangent
space at the identity. Over a field it is consequently finite-dimensional and projective, which
is the finiteness input for the scalar-extension description of the tangent space and the adjoint
representation in the ReductiveGroups roadmap, Layer 2.

## Main declarations

* `TauCeti.Bialgebra.instModuleFiniteCotangentSpace`: the specialization to the counit of a
  finite-type commutative bialgebra.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§12 and 14.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

namespace TauCeti.Bialgebra

open _root_.Bialgebra

variable (R A : Type*) [CommRing R] [CommRing A] [Bialgebra R A]

/-- The cotangent space at the identity of a finite-type commutative bialgebra over a noetherian
base is finite over that base. -/
instance instModuleFiniteCotangentSpace [IsNoetherianRing R] [Algebra.FiniteType R A] :
    Module.Finite R (CotangentSpace R A) := by
  let _ : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  exact AlgHom.finite_cotangent_ker (counitAlgHom R A)

end TauCeti.Bialgebra


