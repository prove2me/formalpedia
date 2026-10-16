-- Prove2me | Definitions.Def_Esgk_IrreduciblePlaneAffineFunctionField
-- name    : Esgk_IrreduciblePlaneAffineFunctionField
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:46:28.072332+00:00
-- url     : https://prove2.me/theorems/ef22fb15-d8e6-42f2-b177-ea279662026e
-- title:
--   Coordinate and function fields of an irreducible plane curve
-- statement:
--   This packages an irreducible bivariate polynomial with its quotient coordinate ring, fraction field, coordinate classes, and coordinate-generation properties.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_IrreduciblePlaneFunctionField
import Mathlib
import Mathlib.AlgebraicGeometry.FunctionField

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

namespace IrreduciblePlanePolynomial

variable {F : Type*} [Field F]

 
abbrev affineScheme (C : IrreduciblePlanePolynomial F) :
    AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Spec (CommRingCat.of C.CoordinateRing)


noncomputable instance affineSchemeFunctionFieldAlgebra
    (C : IrreduciblePlanePolynomial F) :
    Algebra (↥(CommRingCat.of C.CoordinateRing))
      (AlgebraicGeometry.Spec
        (CommRingCat.of C.CoordinateRing)).functionField :=
  RingHom.toAlgebra <| by
    apply CommRingCat.Hom.hom
    apply AlgebraicGeometry.StructureSheaf.toStalk


instance affineSchemeFunctionFieldIsFractionRing
    (C : IrreduciblePlanePolynomial F) :
    IsFractionRing (↥(CommRingCat.of C.CoordinateRing))
      (AlgebraicGeometry.Spec
        (CommRingCat.of C.CoordinateRing)).functionField :=
  AlgebraicGeometry.functionField_isFractionRing_of_affine
    (CommRingCat.of C.CoordinateRing)


noncomputable instance affineSchemeFunctionFieldBaseAlgebra
    (C : IrreduciblePlanePolynomial F) :
    Algebra F
      (AlgebraicGeometry.Spec
        (CommRingCat.of C.CoordinateRing)).functionField :=
  Algebra.compHom _ (algebraMap F C.CoordinateRing)


instance affineSchemeFunctionFieldScalarTower
    (C : IrreduciblePlanePolynomial F) :
    IsScalarTower F (↥(CommRingCat.of C.CoordinateRing))
      (AlgebraicGeometry.Spec
        (CommRingCat.of C.CoordinateRing)).functionField :=
  IsScalarTower.of_algebraMap_eq
    (R := F) (S := ↥(CommRingCat.of C.CoordinateRing))
    (A := (AlgebraicGeometry.Spec
      (CommRingCat.of C.CoordinateRing)).functionField)
    (fun _ => rfl)


end IrreduciblePlanePolynomial

end Esgk


