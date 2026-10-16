-- Prove2me | Definitions.Def_Esgk_IrreduciblePlaneAffineNormalization
-- name    : Esgk_IrreduciblePlaneAffineNormalization
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:48:15.250522+00:00
-- url     : https://prove2.me/theorems/1d361bc3-cb2e-49dc-b146-f1c9f52e3861
-- title:
--   Affine normalization of an irreducible plane curve
-- statement:
--   This packages the affine normalization ring and scheme of an irreducible plane curve together with its injective, integral, integrally closed, and dominant structure maps.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_IrreduciblePlaneAffineFunctionField
import Definitions.Def_Esgk_IrreduciblePlaneFunctionField
import Mathlib
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.AsSubring

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open CategoryTheory

namespace IrreduciblePlanePolynomial

variable {F : Type*} [Field F]


abbrev affineNormalizationRing (C : IrreduciblePlanePolynomial F) :=
  integralClosure C.CoordinateRing C.FunctionField


abbrev affineNormalizationScheme (C : IrreduciblePlanePolynomial F) :
    AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Spec (CommRingCat.of C.affineNormalizationRing)


noncomputable def affineNormalizationMorphism
    (C : IrreduciblePlanePolynomial F) :
    C.affineNormalizationScheme ⟶ C.affineScheme :=
  AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom
      (algebraMap C.CoordinateRing C.affineNormalizationRing))

 
theorem affineNormalizationRing_algebraMap_injective
    (C : IrreduciblePlanePolynomial F) :
    Function.Injective
      (algebraMap C.CoordinateRing C.affineNormalizationRing) :=
  FaithfulSMul.algebraMap_injective _ _

 
instance affineNormalizationMorphismIsIntegral
    (C : IrreduciblePlanePolynomial F) :
    AlgebraicGeometry.IsIntegralHom C.affineNormalizationMorphism := by
  change AlgebraicGeometry.IsIntegralHom
    (AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom
        (algebraMap C.CoordinateRing C.affineNormalizationRing)))
  rw [AlgebraicGeometry.IsIntegralHom.SpecMap_iff]
  exact algebraMap_isIntegral_iff.mpr inferInstance

 
instance affineNormalizationRingIsIntegrallyClosed
    (C : IrreduciblePlanePolynomial F) :
    IsIntegrallyClosed C.affineNormalizationRing :=
  integralClosure.isIntegrallyClosedOfFiniteExtension C.FunctionField

 
noncomputable instance affineNormalizationRingBaseAlgebra
    (C : IrreduciblePlanePolynomial F) :
    Algebra F C.affineNormalizationRing :=
  Algebra.compHom C.affineNormalizationRing
    (algebraMap F C.CoordinateRing)


instance affineNormalizationRingScalarTower
    (C : IrreduciblePlanePolynomial F) :
    IsScalarTower F C.affineNormalizationRing C.FunctionField :=
  IsScalarTower.of_algebraMap_eq
    (R := F) (S := C.affineNormalizationRing) (A := C.FunctionField)
    (fun _ => rfl)

 
noncomputable instance affineNormalizationFunctionFieldAlgebra
    (C : IrreduciblePlanePolynomial F) :
    Algebra (↥(CommRingCat.of C.affineNormalizationRing))
      C.affineNormalizationScheme.functionField :=
  RingHom.toAlgebra <| by
    apply CommRingCat.Hom.hom
    apply AlgebraicGeometry.StructureSheaf.toStalk


instance affineNormalizationFunctionFieldIsFractionRing
    (C : IrreduciblePlanePolynomial F) :
    IsFractionRing C.affineNormalizationRing
      C.affineNormalizationScheme.functionField :=
  AlgebraicGeometry.functionField_isFractionRing_of_affine
    (CommRingCat.of C.affineNormalizationRing)

 
noncomputable instance affineNormalizationFunctionFieldBaseAlgebra
    (C : IrreduciblePlanePolynomial F) :
    Algebra F C.affineNormalizationScheme.functionField :=
  Algebra.compHom _ (algebraMap F C.affineNormalizationRing)


instance affineNormalizationFunctionFieldScalarTower
    (C : IrreduciblePlanePolynomial F) :
    IsScalarTower F C.affineNormalizationRing
      C.affineNormalizationScheme.functionField :=
  IsScalarTower.of_algebraMap_eq
    (R := F) (S := C.affineNormalizationRing)
    (A := C.affineNormalizationScheme.functionField)
    (fun _ => rfl)


theorem affineNormalizationMorphism_appTop_injective
    (C : IrreduciblePlanePolynomial F) :
    Function.Injective C.affineNormalizationMorphism.appTop.hom := by
  intro x y hxy
  have hn := AlgebraicGeometry.Scheme.ΓSpecIso_naturality
    (CommRingCat.ofHom
      (algebraMap C.CoordinateRing C.affineNormalizationRing))
  have hn' := congrArg CommRingCat.Hom.hom hn
  have hx := congrArg (fun k => k x) hn'
  have hy := congrArg (fun k => k y) hn'
  have hxy' :
      (AlgebraicGeometry.Scheme.ΓSpecIso
        (CommRingCat.of C.affineNormalizationRing)).hom.hom
          (C.affineNormalizationMorphism.appTop.hom x) =
      (AlgebraicGeometry.Scheme.ΓSpecIso
        (CommRingCat.of C.affineNormalizationRing)).hom.hom
          (C.affineNormalizationMorphism.appTop.hom y) := by
    rw [hxy]
  have hφeq :
      algebraMap C.CoordinateRing C.affineNormalizationRing
          ((AlgebraicGeometry.Scheme.ΓSpecIso
            (CommRingCat.of C.CoordinateRing)).hom.hom x) =
      algebraMap C.CoordinateRing C.affineNormalizationRing
          ((AlgebraicGeometry.Scheme.ΓSpecIso
            (CommRingCat.of C.CoordinateRing)).hom.hom y) := by
    calc
      _ = _ := hx.symm
      _ = _ := hxy'
      _ = _ := hy
  exact ((ConcreteCategory.isIso_iff_bijective
    (AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of C.CoordinateRing)).hom).mp inferInstance).injective
    (C.affineNormalizationRing_algebraMap_injective hφeq)

 
instance affineNormalizationMorphismIsSchemeTheoreticallyDominant
    (C : IrreduciblePlanePolynomial F) :
    AlgebraicGeometry.IsSchemeTheoreticallyDominant
      C.affineNormalizationMorphism := by
  rw [AlgebraicGeometry.isSchemeTheoreticallyDominant_iff,
    AlgebraicGeometry.Scheme.ker_of_isAffine]
  apply AlgebraicGeometry.Scheme.IdealSheafData.ext_of_isAffine
  simp only [AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop_ideal,
    AlgebraicGeometry.Scheme.IdealSheafData.ideal_bot]
  have hk :
      RingHom.ker C.affineNormalizationMorphism.appTop.hom = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp
      C.affineNormalizationMorphism_appTop_injective
  rw [hk]
  simp


end IrreduciblePlanePolynomial

end Esgk


