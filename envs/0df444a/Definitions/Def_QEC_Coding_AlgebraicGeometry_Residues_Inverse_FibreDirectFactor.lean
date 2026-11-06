-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Inverse_FibreDirectFactor
-- name    : QEC_Coding_AlgebraicGeometry_Residues_Inverse_FibreDirectFactor
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:36:51.651203+00:00
-- url     : https://prove2.me/theorems/d894e365-f72b-4fd7-904c-8041ecc5e0f6
-- title:
--   Fibre Direct Factor
-- statement:
--   Definitions and structural lemmas for Fibre Direct Factor, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Inverse/FibreDirectFactor.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_IntegralDifferentialResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseInfinityFibre
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.InverseFibreDirectFactor
open scoped Polynomial RatFunc
open UniqueFactorizationMonoid
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [oldPolynomialAlgebra : Algebra k[X] F]
variable [oldRationalAlgebra : Algebra k⟮X⟯ F]
variable [oldScalarTower : IsScalarTower k[X] k⟮X⟯ F]
variable [oldFunctionField : _root_.FunctionField k F]
variable [oldSeparable : Algebra.IsSeparable k⟮X⟯ F]
local notation3 "inverseRationalAlgebra" =>
  InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := oldRationalAlgebra) k F
local notation3 "inversePolynomialAlgebra" =>
  InverseAffinePlace.transportedPolynomialAlgebra
    (oldRationalAlgebra := oldRationalAlgebra) k F
local notation3 "inverseScalarTower" =>
  InverseAffinePlace.transportedScalarTower
    (oldRationalAlgebra := oldRationalAlgebra) k F
local notation3 "inverseFunctionField" =>
  InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := oldRationalAlgebra)
    (oldFunctionField := oldFunctionField) k F
local notation3 "inverseIsSeparable" =>
  InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := oldRationalAlgebra)
    (oldSeparable := oldSeparable) k F
noncomputable def infinityFibreEquivDirectFactors :
    letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
    letI : Algebra k[X] F := inversePolynomialAlgebra
    letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
    letI : _root_.FunctionField k F := inverseFunctionField
    letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
    InverseAffinePlace.infinityFibre
        (oldRationalAlgebra := oldRationalAlgebra) k F ≃
      (factors (Ideal.map
        (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F))
        (Polynomial.idealX k).asIdeal)).toFinset := by
  letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
  letI : Algebra k[X] F := inversePolynomialAlgebra
  letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
  letI : _root_.FunctionField k F := inverseFunctionField
  letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
  let B : Type _ := _root_.FunctionField.ringOfIntegers k F
  letI : Module.IsTorsionFree k[X] B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (_root_.FunctionField.ringOfIntegers.algebraMap_injective k F)
  let e := InverseAffinePlace.infinityFibreEquivPrimesOver
    (oldRationalAlgebra := oldRationalAlgebra) k F
  let hs :
      (↑(IsDedekindDomain.primesOverFinset
        (InverseAffinePlace.infinityBasePrime k) B) : Set (Ideal B)) =
        (InverseAffinePlace.infinityBasePrime k).primesOver B :=
    IsDedekindDomain.coe_primesOverFinset
      (InverseAffinePlace.infinityBasePrime_ne_zero k) B
  exact e.trans (Equiv.setCongr hs.symm)
end QEC.Coding.AlgebraicGeometry.InverseFibreDirectFactor


