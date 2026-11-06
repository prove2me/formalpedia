-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseInfinityFibre
-- name    : QEC_Coding_AlgebraicGeometry_Places_InverseInfinityFibre
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:42:58.305795+00:00
-- url     : https://prove2.me/theorems/6937317e-0fe5-4e2f-9ead-c933bc334584
-- title:
--   Inverse Infinity Fibre
-- statement:
--   Definitions and structural lemmas for Inverse Infinity Fibre, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/InverseInfinityFibre.lean

import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffineGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
namespace InverseAffinePlace
open scoped Polynomial RatFunc
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [oldPolynomialAlgebra : Algebra k[X] F]
variable [oldRationalAlgebra : Algebra k⟮X⟯ F]
variable [oldScalarTower : IsScalarTower k[X] k⟮X⟯ F]
variable [oldFunctionField : _root_.FunctionField k F]
variable [oldSeparable : Algebra.IsSeparable k⟮X⟯ F]
local notation3 "inverseRationalAlgebra" =>
  transportedRationalAlgebra (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra)
local notation3 "inversePolynomialAlgebra" =>
  transportedPolynomialAlgebra (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra)
local notation3 "inverseScalarTower" =>
  transportedScalarTower (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra)
local notation3 "inverseFunctionField" =>
  transportedFunctionField (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField)
local notation3 "inverseIsSeparable" =>
  transportedIsSeparable (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable)
local notation3 "inverseCarrier" =>
  carrier (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra)
noncomputable abbrev infinityBasePrime : Ideal k[X] :=
  (Polynomial.idealX k).asIdeal
theorem infinityBasePrime_ne_zero : infinityBasePrime k ≠ 0 := by
  rw [Ideal.zero_eq_bot]
  exact (Polynomial.idealX k).ne_bot
noncomputable abbrev infinityFibre : Type _ :=
  letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
  letI : Algebra k[X] F := inversePolynomialAlgebra
  letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
  letI : _root_.FunctionField k F := inverseFunctionField
  letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
  {v : IsDedekindDomain.HeightOneSpectrum
      (_root_.FunctionField.ringOfIntegers k F) //
    v.asIdeal ∣ Ideal.map
      (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F))
      (infinityBasePrime k)}
noncomputable def infinityFibreEquivPrimesOver :
    letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
    letI : Algebra k[X] F := inversePolynomialAlgebra
    letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
    letI : _root_.FunctionField k F := inverseFunctionField
    letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
    infinityFibre (k := k) (F := F) (oldRationalAlgebra := oldRationalAlgebra) ≃
      (infinityBasePrime k).primesOver (_root_.FunctionField.ringOfIntegers k F) := by
  letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
  letI : Algebra k[X] F := inversePolynomialAlgebra
  letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
  letI : _root_.FunctionField k F := inverseFunctionField
  letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
  letI : Module.IsTorsionFree k[X] F :=
    Module.IsTorsionFree.trans_faithfulSMul k[X] k⟮X⟯ F
  letI : Module.IsTorsionFree k[X] (_root_.FunctionField.ringOfIntegers k F) :=
    IsIntegralClosure.isTorsionFree k[X] F
  letI : Algebra.IsIntegral k[X] (_root_.FunctionField.ringOfIntegers k F) :=
    IsIntegralClosure.isIntegral_algebra k[X] F
  exact IsDedekindDomain.HeightOneSpectrum.equivPrimesOver
    (_root_.FunctionField.ringOfIntegers k F) (infinityBasePrime_ne_zero k)
noncomputable instance infinityFibreFintype :
    letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
    letI : Algebra k[X] F := inversePolynomialAlgebra
    letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
    letI : _root_.FunctionField k F := inverseFunctionField
    letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
    Fintype (infinityFibre (k := k) (F := F) (oldRationalAlgebra := oldRationalAlgebra)) := by
  letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
  letI : Algebra k[X] F := inversePolynomialAlgebra
  letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
  letI : _root_.FunctionField k F := inverseFunctionField
  letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
  letI : Module.IsTorsionFree k[X] F :=
    Module.IsTorsionFree.trans_faithfulSMul k[X] k⟮X⟯ F
  letI : Module.IsTorsionFree k[X] (_root_.FunctionField.ringOfIntegers k F) :=
    IsIntegralClosure.isTorsionFree k[X] F
  letI : Algebra.IsIntegral k[X] (_root_.FunctionField.ringOfIntegers k F) :=
    IsIntegralClosure.isIntegral_algebra k[X] F
  letI : Fintype
      ((infinityBasePrime k).primesOver (_root_.FunctionField.ringOfIntegers k F)) :=
    (IsDedekindDomain.primesOver_finite (infinityBasePrime k)
      (_root_.FunctionField.ringOfIntegers k F)).fintype
  exact Fintype.ofEquiv
    ((infinityBasePrime k).primesOver (_root_.FunctionField.ringOfIntegers k F))
    (infinityFibreEquivPrimesOver (k := k) (F := F)
      (oldRationalAlgebra := oldRationalAlgebra)).symm
noncomputable def globalPlace (v : infinityFibre (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra)) :
    letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
    letI : Algebra k[X] F := inversePolynomialAlgebra
    letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
    letI : _root_.FunctionField k F := inverseFunctionField
    letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
    @GlobalPlace k F _ _ _ (AffinePlace.constantAlgebra k F) := by
  letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
  letI : Algebra k[X] F := inversePolynomialAlgebra
  letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
  letI : _root_.FunctionField k F := inverseFunctionField
  letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
  exact @AffinePlace.globalPlace k F _ _ _ inversePolynomialAlgebra inverseRationalAlgebra
    inverseScalarTower inverseFunctionField inverseIsSeparable v.1
end InverseAffinePlace
end QEC.Coding.AlgebraicGeometry


