-- Prove2me | Definitions.Def_TC433_Algebra_Lie_UniversalEnveloping_Kostant_RootSubgroup_Elementary_Coordinate_4adc31126b
-- name    : TC433_Algebra_Lie_UniversalEnveloping_Kostant_RootSubgroup_Elementary_Coordinate_4adc31126b
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:02:18.940202+00:00
-- url     : https://prove2.me/theorems/b054f9dd-6405-4d75-9bcc-e84ab10075e1
-- title:
--   TauCeti: Algebra / Lie / UniversalEnveloping / Kostant / RootSubgroup / Elementary / Coordinate
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Elementary.Coordinate for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/Algebra/Lie/UniversalEnveloping/Kostant/RootSubgroup/Elementary/Coordinate.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Definitions.Def_TC433_Algebra_Lie_UniversalEnveloping_Kostant_RootSubgroup_Coordinate_7e8f6685d2
public import Definitions.Def_TC433_Algebra_Lie_UniversalEnveloping_Kostant_RootSubgroup_Elementary_Basic_fec652dcce

/-!
# Matrix coordinates of the parametrized Kostant root subgroups

The root subgroup map `x_α` with its parameter read in the value ring, `kostantRootSubgroupParam`,
takes values in the automorphisms of a scalar extension `A ⊗[ℤ] M`. A finite basis
`b : Basis η ℤ M` turns those automorphisms into invertible matrices, and
`kostantRootSubgroupMatrix` is the resulting matrix-valued root subgroup. This file compares the
two: in the coordinates of `b.baseChange A`, a parametrized root-subgroup element is exactly its
represented root-subgroup matrix.

The comparison involves neither the represented `GLₙ` presentation nor any group scheme, so it is
stated for an arbitrary finite basis index and lives below the scheme layer.

## Main declarations

* `TauCeti.UniversalEnvelopingAlgebra.basisMatrix_kostantRootSubgroupParam`: in basis coordinates,
  a parametrized Kostant root-subgroup element is its represented root-subgroup matrix.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §4.4.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TensorProduct WithConv

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {ι : Type*} {κ : Type*}
variable {V : Type*} [AddCommGroup V] [Module ℚ V]

variable (e : ι → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M)
variable (hnil : ∀ i, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable {η : Type*} [Fintype η] [DecidableEq η] (b : Module.Basis η ℤ M)

-- Match tensor products to the `ℤ`-algebra instance stored by `CommAlgCat` objects.
attribute [local instance high] Algebra.toModule

/-- In basis coordinates, a parametrized Kostant root-subgroup element is its represented
root-subgroup matrix. -/
@[simp]
theorem basisMatrix_kostantRootSubgroupParam
    (A : Type v) [CommRing A] (i : ι) (t : Multiplicative A) :
    Units.map (LinearMap.toMatrixAlgEquiv (b.baseChange A)).toMulEquiv
        (kostantRootSubgroupParam e h ρ M hM i (hnil i) (CommAlgCat.of ℤ A) t) =
      kostantRootSubgroupMatrix e h ρ M hM i (hnil i) b
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm t) := by
  rw [kostantRootSubgroupMatrix_def, MonoidHom.comp_apply,
    kostantRootSubgroupParam_apply, MulEquiv.toMonoidHom_eq_coe]

end TauCeti.UniversalEnvelopingAlgebra


