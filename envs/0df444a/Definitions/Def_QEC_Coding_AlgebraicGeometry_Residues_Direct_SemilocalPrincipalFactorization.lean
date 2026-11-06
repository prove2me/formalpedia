-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SemilocalPrincipalFactorization
-- name    : QEC_Coding_AlgebraicGeometry_Residues_Direct_SemilocalPrincipalFactorization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:47:10.570118+00:00
-- url     : https://prove2.me/theorems/90b0464c-9fcf-4f56-af5b-487975d43a89
-- title:
--   Semilocal Principal Factorization
-- statement:
--   Definitions and structural lemmas for Semilocal Principal Factorization, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/SemilocalPrincipalFactorization.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SemilocalUniformizer
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.DirectSemilocalPrincipalFactorization
open scoped Polynomial RatFunc nonZeroDivisors BigOperators
open UniqueFactorizationMonoid
open DirectIntegralDifferentialResidue
open DirectFactorSemilocalLogarithmicResidue
open DirectSemilocalUniformizer
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
noncomputable local instance _p2m_local_instance_698d2271dc_39 : Algebra k F := AffinePlace.constantAlgebra k F
abbrev R : Type _ := k[X]
abbrev B : Type _ := _root_.FunctionField.ringOfIntegers k F
local instance _p2m_local_instance_698d2271dc_44 : Module.IsTorsionFree (R k) (B k F) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (_root_.FunctionField.ringOfIntegers.algebraMap_injective k F)
end QEC.Coding.AlgebraicGeometry.DirectSemilocalPrincipalFactorization


