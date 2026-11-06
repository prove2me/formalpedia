-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RatFuncInverseInfinityValuation
-- name    : QEC_Coding_AlgebraicGeometry_Places_RatFuncInverseInfinityValuation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T20:06:13.87132+00:00
-- url     : https://prove2.me/theorems/81118818-1e7a-4c6f-b2a7-6e4cfe0012ad
-- title:
--   Rat Func Inverse Infinity Valuation
-- statement:
--   Definitions and structural lemmas for Rat Func Inverse Infinity Valuation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RatFuncInverseInfinityValuation.lean

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalFieldPlaces
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_globalPlace_surjective
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseAffinePlace_globalPlace_surjective

set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.RatFuncInverseInfinityValuation
open scoped Polynomial RatFunc WithZero
open RatFuncFixturePlaces
abbrev K : Type := RatFuncFixturePlaces.K
abbrev F : Type := RatFuncFixturePlaces.F
local instance _p2m_local_instance_de9b108ef9_13 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
noncomputable local instance oldRationalAlgebra : Algebra K⟮X⟯ F :=
  RatFuncFixturePlaces.oldRationalAlgebra
noncomputable local instance oldPolynomialAlgebra : Algebra K[X] F :=
  RatFuncFixturePlaces.oldPolynomialAlgebra
noncomputable local instance oldScalarTower : IsScalarTower K[X] K⟮X⟯ F :=
  RatFuncFixturePlaces.oldScalarTower
noncomputable local instance oldFunctionField : _root_.FunctionField K F :=
  RatFuncFixturePlaces.oldFunctionField
noncomputable local instance oldSeparable : Algebra.IsSeparable K⟮X⟯ F :=
  RatFuncFixturePlaces.oldSeparable
noncomputable local instance oldFractionRing :
    @IsFractionRing K[X] _ F _ oldPolynomialAlgebra := inferInstance
noncomputable local instance ratFuncDecidableEq : DecidableEq K⟮X⟯ := Classical.decEq _
attribute [local instance] ratFuncDecidableEq
abbrev inverseScalarTowerType : Prop :=
  @IsScalarTower K[X] K⟮X⟯ F RatFunc.instSMulOfFractionRingPolynomial
    (InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) K F).toSMul
    (InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := oldRationalAlgebra) K F).toSMul
noncomputable def inverseXFibreValuation : Valuation F ℤᵐ⁰ := by
  letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
  letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
  letI : Algebra K F := AffinePlace.constantAlgebra K F
  exact (InverseAffinePlace.globalPlace
    (oldRationalAlgebra := RatFuncFixturePlaces.oldRationalAlgebra)
    (oldFunctionField := RatFuncFixturePlaces.oldFunctionField)
    (oldSeparable := RatFuncFixturePlaces.oldSeparable)
    K F inverseXFibrePoint).valuation
theorem inverseXFibreValuation_surjective :
    Function.Surjective inverseXFibreValuation := by
  letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
  letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
  letI : Algebra K F := AffinePlace.constantAlgebra K F
  unfold inverseXFibreValuation
  exact InverseAffinePlace.globalPlace_surjective
    (oldPolynomialAlgebra := RatFuncFixturePlaces.oldPolynomialAlgebra)
    (oldRationalAlgebra := RatFuncFixturePlaces.oldRationalAlgebra)
    (oldScalarTower := RatFuncFixturePlaces.oldScalarTower)
    (oldFunctionField := RatFuncFixturePlaces.oldFunctionField)
    (oldSeparable := RatFuncFixturePlaces.oldSeparable)
    K F inverseXFibrePoint
noncomputable def inverseXFibreGlobalPlace : GlobalPlace K F where
  valuation := inverseXFibreValuation
  normalized := inverseXFibreValuation_surjective
end QEC.Coding.AlgebraicGeometry.RatFuncInverseInfinityValuation


