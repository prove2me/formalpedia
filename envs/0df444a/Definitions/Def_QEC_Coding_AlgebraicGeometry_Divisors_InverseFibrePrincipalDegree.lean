-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_InverseFibrePrincipalDegree
-- name    : QEC_Coding_AlgebraicGeometry_Divisors_InverseFibrePrincipalDegree
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:17:47.044935+00:00
-- url     : https://prove2.me/theorems/18d889b5-ab43-4061-9eca-d0b81f640aa0
-- title:
--   Inverse Fibre Principal Degree
-- statement:
--   Definitions and structural lemmas for Inverse Fibre Principal Degree, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/InverseFibrePrincipalDegree.lean

import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlaceDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_AffinePrincipalDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseInfinityFibre
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_DirectNormCount
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_DirectRelNormCoefficient
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Inverse_RationalInfinityTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.InverseFibrePrincipalDegree
open scoped BigOperators Polynomial RatFunc WithZero nonZeroDivisors
open UniqueFactorizationMonoid
open Submodule.IsPrincipal
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [oldPolynomialAlgebra : Algebra k[X] F]
variable [oldRationalAlgebra : Algebra k⟮X⟯ F]
variable [oldScalarTower : IsScalarTower k[X] k⟮X⟯ F]
variable [oldFunctionField : _root_.FunctionField k F]
variable [oldSeparable : Algebra.IsSeparable k⟮X⟯ F]
local notation3 "R" => k[X]
noncomputable abbrev inverseRingOfIntegers
    (oldPolynomialAlgebra : Algebra k[X] F) (oldRationalAlgebra : Algebra k⟮X⟯ F)
    (oldScalarTower : IsScalarTower k[X] k⟮X⟯ F)
    (oldFunctionField : _root_.FunctionField k F)
    (oldSeparable : Algebra.IsSeparable k⟮X⟯ F) : Type _ := by
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := oldRationalAlgebra) k F
  letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (oldRationalAlgebra := oldRationalAlgebra) k F
  letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
    (oldRationalAlgebra := oldRationalAlgebra) k F
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) k F
  letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) k F
  exact ↥(_root_.FunctionField.ringOfIntegers k F)
local notation3 "B" => inverseRingOfIntegers
  (oldPolynomialAlgebra := oldPolynomialAlgebra) (oldRationalAlgebra := oldRationalAlgebra)
  (oldScalarTower := oldScalarTower) (oldFunctionField := oldFunctionField)
  (oldSeparable := oldSeparable) k F
local instance inverseFibrePrincipalDegree_isTorsionFree : Module.IsTorsionFree R B := by
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := oldRationalAlgebra) k F
  letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (oldRationalAlgebra := oldRationalAlgebra) k F
  letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
    (oldRationalAlgebra := oldRationalAlgebra) k F
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) k F
  letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) k F
  exact Module.isTorsionFree_iff_algebraMap_injective.mpr
    (_root_.FunctionField.ringOfIntegers.algebraMap_injective k F)
attribute [local instance] inverseFibrePrincipalDegree_isTorsionFree
noncomputable abbrev inverseFibrePrincipalDivisor (f : Fˣ) :
    Divisor (InverseAffinePlace.infinityFibre
      (oldRationalAlgebra := oldRationalAlgebra) k F) :=
  InverseAffinePlace.infinityFibrePrincipalDivisor
    (π := oldPolynomialAlgebra) (ρ := oldRationalAlgebra) (τ := oldScalarTower)
    (φ := oldFunctionField) (σ := oldSeparable) (k := k) (F := F) f
noncomputable abbrev inverseFibreResidueDegree
    (D : InverseAffinePlace.infinityFibre
      (oldRationalAlgebra := oldRationalAlgebra) k F) : Nat :=
  InverseAffinePlace.infinityFibreResidueDegree
    (π := oldPolynomialAlgebra) (ρ := oldRationalAlgebra) (τ := oldScalarTower)
    (φ := oldFunctionField) (σ := oldSeparable) (k := k) (F := F) D
noncomputable abbrev xPrime : Ideal R := InverseAffinePlace.infinityBasePrime k
end QEC.Coding.AlgebraicGeometry.InverseFibrePrincipalDegree


