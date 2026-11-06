-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_DirectRelNormCoefficient
-- name    : QEC_Coding_AlgebraicGeometry_Divisors_DirectRelNormCoefficient
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T13:07:05.514831+00:00
-- url     : https://prove2.me/theorems/5d37eb68-b695-4e07-8015-f90b7eae114a
-- title:
--   Direct Rel Norm Coefficient
-- statement:
--   Definitions and structural lemmas for Direct Rel Norm Coefficient, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/DirectRelNormCoefficient.lean

import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlaceDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_DirectNormCount
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_SeparableNormalCover
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.DirectRelNormCoefficient
open scoped BigOperators Polynomial RatFunc nonZeroDivisors
open UniqueFactorizationMonoid
section finite_collection
variable {alpha beta : Type*} [DecidableEq alpha] [DecidableEq beta]
end finite_collection
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
abbrev directRingOfIntegers : Type _ := _root_.FunctionField.ringOfIntegers k F
local notation3 "R" => k[X]
local notation3 "B" => directRingOfIntegers k F
local instance directRelNormCoefficient_isTorsionFree : Module.IsTorsionFree R B :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (_root_.FunctionField.ringOfIntegers.algebraMap_injective k F)
attribute [local instance] directRelNormCoefficient_isTorsionFree
end QEC.Coding.AlgebraicGeometry.DirectRelNormCoefficient


