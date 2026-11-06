-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SemilocalCokernelTraceSum
-- name    : QEC_Coding_AlgebraicGeometry_Residues_Direct_SemilocalCokernelTraceSum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:48:05.442643+00:00
-- url     : https://prove2.me/theorems/0464911c-3bab-458a-94ab-1f693469e334
-- title:
--   Semilocal Cokernel Trace Sum
-- statement:
--   Definitions and structural lemmas for Semilocal Cokernel Trace Sum, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/SemilocalCokernelTraceSum.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorPrimaryTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SemilocalPrincipalFactorization
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CoprimeQuotientTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CRTTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrincipalCokernelTrace
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.DirectSemilocalCokernelTraceSum
open scoped Polynomial RatFunc nonZeroDivisors BigOperators
open UniqueFactorizationMonoid
attribute [-instance] Ideal.Quotient.commSemiring
attribute [local instance]
  Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
noncomputable local instance _p2m_local_instance_fa03a56197_45 : Algebra k F := AffinePlace.constantAlgebra k F
abbrev R : Type _ := k[X]
abbrev B : Type _ := _root_.FunctionField.ringOfIntegers k F
local instance _p2m_local_instance_fa03a56197_50 : Module.IsTorsionFree (R k) (B k F) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (_root_.FunctionField.ringOfIntegers.algebraMap_injective k F)
end QEC.Coding.AlgebraicGeometry.DirectSemilocalCokernelTraceSum


