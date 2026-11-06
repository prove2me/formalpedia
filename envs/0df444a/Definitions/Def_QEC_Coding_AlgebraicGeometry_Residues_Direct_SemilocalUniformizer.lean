-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SemilocalUniformizer
-- name    : QEC_Coding_AlgebraicGeometry_Residues_Direct_SemilocalUniformizer
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:42:51.612315+00:00
-- url     : https://prove2.me/theorems/f7f91d77-6721-4d64-a322-a8283a78228c
-- title:
--   Semilocal Uniformizer
-- statement:
--   Definitions and structural lemmas for Semilocal Uniformizer, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/SemilocalUniformizer.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalLogarithmicResidue
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.DirectSemilocalUniformizer
open scoped Polynomial RatFunc nonZeroDivisors BigOperators
open UniqueFactorizationMonoid
open DirectIntegralDifferentialResidue
open DirectFactorSemilocalLogarithmicResidue
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
noncomputable local instance _p2m_local_instance_46770e045f_37 : Algebra k F := AffinePlace.constantAlgebra k F
abbrev R : Type _ := k[X]
abbrev B : Type _ := _root_.FunctionField.ringOfIntegers k F
local instance _p2m_local_instance_46770e045f_42 : Module.IsTorsionFree (R k) (B k F) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (_root_.FunctionField.ringOfIntegers.algebraMap_injective k F)
end QEC.Coding.AlgebraicGeometry.DirectSemilocalUniformizer


