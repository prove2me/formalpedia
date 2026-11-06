-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalCokernelTrace
-- name    : QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalCokernelTrace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:26:48.81041+00:00
-- url     : https://prove2.me/theorems/3c1a984e-7a53-4014-a20d-76798755e6cd
-- title:
--   Factor Semilocal Cokernel Trace
-- statement:
--   Definitions and structural lemmas for Factor Semilocal Cokernel Trace, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/FactorSemilocalCokernelTrace.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalPrimaryTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalMultiplier
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrincipalCokernelTrace
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalCokernelTrace
open scoped Polynomial RatFunc nonZeroDivisors
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
abbrev R : Type _ := k[X]
abbrev B : Type _ := _root_.FunctionField.ringOfIntegers k F
local instance _p2m_local_instance_d1e0a01c5a_46 : Module.IsTorsionFree (R k) (B k F) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (_root_.FunctionField.ringOfIntegers.algebraMap_injective k F)
end QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalCokernelTrace


