-- Prove2me | Definitions.Def_TC433_Algebra_AlgebraicGroup_Tangent_Naturality_a31c8e6405
-- name    : TC433_Algebra_AlgebraicGroup_Tangent_Naturality_a31c8e6405
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:23:05.703284+00:00
-- url     : https://prove2.me/theorems/f17b7ba5-b567-4e7d-a71a-200bf29f7d77
-- title:
--   TauCeti: Algebra / AlgebraicGroup / Tangent / Naturality
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.Algebra.AlgebraicGroup.Tangent.Naturality for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/Algebra/AlgebraicGroup/Tangent/Naturality.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Definitions.Def_TC433_Algebra_AlgebraicGroup_Tangent_Adjoint_0abc0d796c

/-!
# Naturality of the tangent and adjoint actions in the coefficient algebra

For a bialgebra `A` over `R`, the tangent space is naturally a functor of the
coefficient algebra:

`B ↦ Derivation R A (Bialgebra.CounitAlgebra R A B)`.

An `R`-algebra homomorphism `φ : B →ₐ[R] C` postcomposes a counit-valued
derivation. The underlying maps of counit algebras are defined in `Tangent.Basic`;
this file packages postcomposition as `Derivation.mapValue`, proves its
functoriality, and, when `A` is a Hopf algebra, shows that it intertwines the adjoint
actions at `B` and `C`.
Together, these statements make the valuewise representations in
`Tangent.Adjoint` into a natural action on the Lie functor.

## Main declarations

* `TauCeti.Bialgebra.CounitAlgebra.mapAlgHom`: the coefficient algebra map.
* `TauCeti.Bialgebra.CounitAlgebra.map`: the same map, linear over the bialgebra
  through the counit actions.
* `Derivation.mapValue`: postcomposition of counit-valued derivations.
* `Derivation.mapValue_adDerivation`: the adjoint action commutes with
  change of coefficient algebra.

The Lie-bracket compatibility, which requires additive inverses, is in
`Tangent.Lie.Naturality`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §14.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

namespace Derivation

open TauCeti _root_.Coalgebra WithConv

variable {R A B C : Type*} [CommSemiring R] [CommSemiring A]

section Bialgebra

variable [Bialgebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

/-- Postcomposition of a counit-valued derivation along an algebra homomorphism of
coefficients. This is the functorial map on tangent vectors. -/
noncomputable def mapValue (phi : B →ₐ[R] C) :
    Derivation R A (Bialgebra.CounitAlgebra R A B) →ₗ[R]
      Derivation R A (Bialgebra.CounitAlgebra R A C) :=
  (Bialgebra.CounitAlgebra.map
    (R := R) (A := A) (B := B) (C := C) phi).compDer |>.restrictScalars R

/-- Postcomposition of a counit-valued derivation acts pointwise. -/
@[simp]
lemma mapValue_apply (phi : B →ₐ[R] C)
    (d : Derivation R A (Bialgebra.CounitAlgebra R A B)) (a : A) :
    mapValue phi d a = phi (d a) := by
  simp only [mapValue, LinearMap.coe_restrictScalars, Derivation.coe_comp,
    LinearMap.comp_apply, Derivation.coeFn_coe, Bialgebra.CounitAlgebra.map_apply]

/-- On underlying linear maps, change of coefficients is postcomposition by the
coefficient algebra map. -/
@[simp]
lemma coe_mapValue_linearMap (phi : B →ₐ[R] C)
    (d : Derivation R A (Bialgebra.CounitAlgebra R A B)) :
    ↑(mapValue phi d) =
      (Bialgebra.CounitAlgebra.mapAlgHom (A := A) phi).toLinearMap.comp
        (↑d : A →ₗ[R] Bialgebra.CounitAlgebra R A B) := by
  ext a
  -- Extensionality presents the left side through its underlying linear map;
  -- `mapValue_apply` is stated through the derivation coercion.
  change mapValue phi d a = _
  rw [mapValue_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    Bialgebra.CounitAlgebra.mapAlgHom_apply]
  rfl

/-- Postcomposition by the identity is the identity on counit-valued derivations. -/
@[simp]
theorem mapValue_id :
    mapValue (A := A) (AlgHom.id R B) =
      LinearMap.id (R := R)
        (M := Derivation R A (Bialgebra.CounitAlgebra R A B)) := by
  ext d a
  simp [mapValue]

/-- Postcomposition of counit-valued derivations preserves composition. -/
@[simp]
theorem mapValue_comp {D : Type*} [Semiring D] [Algebra R D]
    (psi : C →ₐ[R] D) (phi : B →ₐ[R] C) :
    mapValue (A := A) (psi.comp phi) =
      (mapValue (A := A) psi).comp (mapValue (A := A) phi) := by
  ext d a
  simp [mapValue]

end Bialgebra

section Adjoint

variable [HopfAlgebra R A] [CommSemiring B] [Algebra R B]
  [CommSemiring C] [Algebra R C]

/-- **The adjoint action is natural in the coefficient algebra.** Mapping a point and
a tangent vector along `phi` and then applying the adjoint action gives the same
result as applying the action first and postcomposing the resulting derivation. -/
@[simp]
theorem mapValue_adDerivation (phi : B →ₐ[R] C)
    (g : WithConv (A →ₐ[R] Bialgebra.CounitAlgebra R A B))
    (d : Derivation R A (Bialgebra.CounitAlgebra R A B)) :
    mapValue phi (adDerivation B g d) =
      adDerivation C
        (AlgHom.mapValue (R := R) (H := A)
          (Bialgebra.CounitAlgebra.mapAlgHom
            (R := R) (A := A) (B := B) (C := C) phi) g)
        (mapValue phi d) := by
  ext a
  rw [mapValue_apply, adDerivation_apply, adDerivation_apply]
  rw [← Bialgebra.CounitAlgebra.mapAlgHom_apply (A := A) phi]
  -- The algebra-hom coercion and its underlying linear map agree pointwise; the
  -- convolution distribution lemma is stated for the latter.
  change (Bialgebra.CounitAlgebra.mapAlgHom (A := A) phi).toLinearMap
      ((toConv g.ofConv.toLinearMap *
          toConv (↑d : A →ₗ[R] Bialgebra.CounitAlgebra R A B) *
          toConv ((g⁻¹).ofConv.toLinearMap)).ofConv a) = _
  rw [← LinearMap.comp_apply
    (Bialgebra.CounitAlgebra.mapAlgHom (A := A) phi).toLinearMap]
  rw [LinearMap.algHom_comp_convMul_distrib, LinearMap.algHom_comp_convMul_distrib]
  simp only [AlgHom.mapValue_apply, coe_mapValue_linearMap, AlgHom.comp_toLinearMap,
    toConv_ofConv, WithConv.convInv_def, AlgHom.toLinearMap_antipodeComp,
    LinearMap.comp_assoc]

end Adjoint

end Derivation


