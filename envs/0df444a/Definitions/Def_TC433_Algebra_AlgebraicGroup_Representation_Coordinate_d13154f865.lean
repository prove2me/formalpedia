-- Prove2me | Definitions.Def_TC433_Algebra_AlgebraicGroup_Representation_Coordinate_d13154f865
-- name    : TC433_Algebra_AlgebraicGroup_Representation_Coordinate_d13154f865
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:10:42.079223+00:00
-- url     : https://prove2.me/theorems/7798e8bb-6567-4c81-b374-d2f28b14d161
-- title:
--   TauCeti: Algebra / AlgebraicGroup / Representation / Coordinate
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.Algebra.AlgebraicGroup.Representation.Coordinate for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/Algebra/AlgebraicGroup/Representation/Coordinate.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.RingTheory.Coalgebra.CoassocSimps
public import Definitions.Def_TC433_Algebra_AlgebraicGroup_GeneralLinear_Coordinate_HopfAlgebra_e646a2f9aa
public import Definitions.Def_TC433_Algebra_AlgebraicGroup_GeneralLinear_FunctorOfPoints_45e74c63fa
public import Definitions.Def_TC433_Algebra_Coalgebra_Comodule_Corestrict_82de27b9df
public import Definitions.Def_TC433_Algebra_Coalgebra_Comodule_MatrixCoefficient_Matrix_a86ead5705
import Definitions.Def_TC433_Algebra_HopfAlgebra_Basic_524b0b4427

/-!
# The coordinate morphism of a finite free comodule

A right comodule over a commutative Hopf algebra `H` with a basis indexed by `Fin n` has a
coefficient matrix over `H`, whose determinant is a unit
(`TauCeti.Comodule.isUnit_det_coefficientMatrix`). Evaluation on that matrix therefore extends
from the matrix monoid coordinate ring to the coordinate ring of `GLₙ`, and the coalgebra
identities satisfied by the coefficient matrix say exactly that the extension is a morphism of
bialgebras

```text
O(GLₙ) ⟶ H.
```

This is the coordinate-ring morphism opposite to the representation of the affine group
represented by `H` on the chosen basis. Its surjectivity is the algebraic condition which the
faithful-representation criterion identifies with a closed immersion into `GLₙ`.

## Main declarations

* `TauCeti.Comodule.coordinateBialgHom`: the induced morphism `O(GLₙ) ⟶ H`.
* `TauCeti.Comodule.coordinateBialgHom_X`: the coordinate morphism sends the generic entry
  `Xᵢⱼ` to the corresponding coefficient-matrix entry.
* `AlgHom.pointsMulEquiv_comp_coordinateBialgHom`: evaluating the coordinate morphism
  gives the coefficient matrix mapped through the evaluating algebra morphism.
* `TauCeti.Comodule.coordinateBialgHom_antipode_X`: its value on the antipode generators.
* `TauCeti.Comodule.coordinateBialgHom_corestrict`: its compatibility with corestriction.
* `TauCeti.Comodule.coordinateBialgHom_eq_unit_comp_counit_of_coact_eq_tmul_one`: its value for
  a trivial coaction.

## References

This is the standard coordinate morphism of a finite free representation; see J. S.
Milne, *Algebraic Groups* (2017), Chapter 4, especially Remark 4.1 and Theorem 4.9.  It advances
`ReductiveGroups/README.md`, Layer 1, "Faithfulness done right".
-/

public section
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct
open Coalgebra Module WithConv

namespace TauCeti.Comodule

universe u v w x

noncomputable section

variable {R : Type u} {H : Type v} {M : Type w}
variable [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [AddCommMonoid M] [Module R M] [Comodule R H M]
variable {n : ℕ}

/-- The algebra morphism underlying the coordinate bialgebra morphism. -/
private def coordinateAlgHom (b : Basis (Fin n) R M) :
    GeneralLinear.coordinateHopfAlgebra R n →ₐ[R] H :=
  (GeneralLinear.generalLinearToPoint (R := R) n
    (Matrix.GeneralLinearGroup.mk'' (coefficientMatrix (C := H) b)
      (isUnit_det_coefficientMatrix (C := H) b))).ofConv

@[simp]
private theorem coordinateAlgHom_X (b : Basis (Fin n) R M) (i j : Fin n) :
    coordinateAlgHom (H := H) b
        (GeneralLinear.coordinateHopfAlgebraAlgEquiv R n
          (GeneralLinear.coordinateRingMap R n (MvPolynomial.X (i, j)))) =
      coefficientMatrix (C := H) b i j := by
  simp only [coordinateAlgHom, GeneralLinear.generalLinearToPoint_apply,
    Matrix.GeneralLinearGroup.val_mk'']

private theorem coordinateAlgHom_counit (b : Basis (Fin n) R M) :
    (Bialgebra.counitAlgHom R H).comp (coordinateAlgHom (H := H) b) =
      Bialgebra.counitAlgHom R (GeneralLinear.coordinateHopfAlgebra R n) := by
  apply GeneralLinear.coordinateHopfAlgebra_algHom_ext R n
  intro i j
  simp only [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, coordinateAlgHom_X,
    counit_coefficientMatrix, GeneralLinear.coordinateHopfAlgebra_counit_X]

private theorem coordinateAlgHom_comul (b : Basis (Fin n) R M) :
    (Algebra.TensorProduct.map (coordinateAlgHom (H := H) b) (coordinateAlgHom (H := H) b)).comp
        (Bialgebra.comulAlgHom R (GeneralLinear.coordinateHopfAlgebra R n)) =
      (Bialgebra.comulAlgHom R H).comp (coordinateAlgHom (H := H) b) := by
  apply GeneralLinear.coordinateHopfAlgebra_algHom_ext R n
  intro i j
  simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply,
    GeneralLinear.coordinateHopfAlgebra_comul_X, map_sum,
    Algebra.TensorProduct.map_tmul, coordinateAlgHom_X]
  exact (comul_coefficientMatrix_eq_sum (C := H) b i j).symm

/-- The coordinate Hopf-algebra morphism associated to a comodule with a basis indexed by
`Fin n`.

Contravariantly, this is the morphism from the affine group represented by `H` to `GLₙ`
defined by the corresponding representation. -/
def coordinateBialgHom (b : Basis (Fin n) R M) :
    GeneralLinear.coordinateHopfAlgebra R n →ₐc[R] H :=
  BialgHom.ofAlgHom (coordinateAlgHom b) (coordinateAlgHom_counit b)
    (coordinateAlgHom_comul b)

/-- The coordinate Hopf-algebra morphism sends a generic matrix entry to the corresponding
coefficient-matrix entry. -/
@[simp]
theorem coordinateBialgHom_X (b : Basis (Fin n) R M) (i j : Fin n) :
    coordinateBialgHom (H := H) b
        (GeneralLinear.coordinateHopfAlgebraAlgEquiv R n
          (GeneralLinear.coordinateRingMap R n (MvPolynomial.X (i, j)))) =
      coefficientMatrix (C := H) b i j := by
  simp only [coordinateBialgHom, BialgHom.ofAlgHom_apply, coordinateAlgHom_X]

/-- Evaluating a representation's coordinate morphism through an algebra morphism gives its
coefficient matrix mapped through that morphism. -/
theorem _root_.AlgHom.pointsMulEquiv_comp_coordinateBialgHom
    {K : Type x} [CommRing K] [Algebra R K]
    (f : H →ₐ[R] K) (b : Module.Basis (Fin n) R M) :
    (GeneralLinear.pointsMulEquiv n
        (WithConv.toConv (f.comp (coordinateBialgHom (H := H) b).toAlgHom)) :
      Matrix (Fin n) (Fin n) K) =
      (coefficientMatrix (C := H) b).map f := by
  ext i j
  rw [GeneralLinear.pointsMulEquiv_apply, GeneralLinear.pointToGeneralLinear_apply,
    WithConv.ofConv_toConv, AlgHom.comp_apply]
  erw [coordinateBialgHom_X]
  rw [Matrix.map_apply]

/-- The coordinate Hopf-algebra morphism sends an antipode generator of `O(GLₙ)` — an entry of
the inverse of the localized generic matrix — to the antipode of the corresponding
coefficient-matrix entry. -/
@[simp]
theorem coordinateBialgHom_antipode_X (b : Basis (Fin n) R M) (i j : Fin n) :
    coordinateBialgHom (H := H) b
        (GeneralLinear.coordinateHopfAlgebraAlgEquiv R n
          ((GeneralLinear.localizedGenericMatrix R n)⁻¹ i j)) =
      HopfAlgebra.antipode R (coefficientMatrix (C := H) b i j) := by
  rw [← GeneralLinear.coordinateHopfAlgebra_antipode_X, BialgHomClass.map_antipode,
    coordinateBialgHom_X]

section Corestrict

variable {K : Type x} [CommRing K] [HopfAlgebra R K]

/-- The coordinate morphism of a comodule corestricted along a bialgebra morphism is the
composite of the original coordinate morphism with that bialgebra morphism. -/
@[simp]
theorem coordinateBialgHom_corestrict (f : H →ₐc[R] K) (b : Basis (Fin n) R M) :
    letI : Comodule R K M := Corestrict f.toCoalgHom
    coordinateBialgHom (H := K) b = f.comp (coordinateBialgHom (H := H) b) := by
  let _ : Comodule R K M := Corestrict f.toCoalgHom
  apply BialgHom.ext
  intro z
  have hAlg : (coordinateBialgHom (H := K) b).toAlgHom =
      (f.comp (coordinateBialgHom (H := H) b)).toAlgHom := by
    apply GeneralLinear.coordinateHopfAlgebra_algHom_ext R n
    intro i j
    rw [BialgHom.comp_toAlgHom, AlgHom.comp_apply]
    erw [coordinateBialgHom_X (H := K), coordinateBialgHom_X (H := H)]
    rw [coefficientMatrix_apply, coefficientMatrix_apply,
      matrixCoefficient_def, matrixCoefficient_def, corestrict_coact_apply]
    have h := LinearMap.congr_fun
      (CoassocSimps.lid_comp_map (b.coord i) f.toLinearMap)
      (coact (R := R) (C := H) (M := M) (b j))
    rw [TensorProduct.map_map, LinearMap.id_comp, LinearMap.comp_id]
    -- `lid_comp_map` states naturality for the underlying linear map; expose that coercion on
    -- the right-hand side after tensor-map composition has been normalized.
    change _ = f.toLinearMap _
    exact h
  exact DFunLike.congr_fun hAlg z

end Corestrict

/-- If every vector has trivial coaction, the coordinate morphism of the representation factors
through the counit of `O(GLₙ)` and the unit of the coefficient Hopf algebra. -/
@[simp]
theorem coordinateBialgHom_eq_unit_comp_counit_of_coact_eq_tmul_one
    (b : Basis (Fin n) R M)
    (htrivial : ∀ m : M, coact (R := R) (C := H) m = m ⊗ₜ[R] (1 : H)) :
    coordinateBialgHom (H := H) b =
      (Bialgebra.unitBialgHom R H).comp
        (Bialgebra.counitBialgHom R (GeneralLinear.coordinateHopfAlgebra R n)) := by
  apply BialgHom.ext
  intro z
  have hAlg : (coordinateBialgHom (H := H) b).toAlgHom =
      ((Bialgebra.unitBialgHom R H).comp
        (Bialgebra.counitBialgHom R
          (GeneralLinear.coordinateHopfAlgebra R n))).toAlgHom := by
    apply GeneralLinear.coordinateHopfAlgebra_algHom_ext R n
    intro i j
    rw [BialgHom.comp_toAlgHom, AlgHom.comp_apply]
    erw [coordinateBialgHom_X]
    rw [coefficientMatrix_apply, matrixCoefficient_def, htrivial]
    by_cases hij : i = j <;> simp [hij]
  exact DFunLike.congr_fun hAlg z

end

end TauCeti.Comodule


