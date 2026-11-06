-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SemilocalDenominator
-- name    : QEC_Coding_AlgebraicGeometry_Residues_Direct_SemilocalDenominator
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:37:16.827295+00:00
-- url     : https://prove2.me/theorems/292446f2-ae8c-4328-8fbe-629a5e313f93
-- title:
--   Semilocal Denominator
-- statement:
--   Definitions and structural lemmas for Semilocal Denominator, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/SemilocalDenominator.lean

import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_IntegralDifferentialResidue
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.DirectSemilocalDenominator
open scoped Polynomial RatFunc nonZeroDivisors
open Submodule.IsPrincipal UniqueFactorizationMonoid
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
noncomputable local instance _p2m_local_instance_ebdac87835_36 : Algebra k F := AffinePlace.constantAlgebra k F
abbrev R : Type _ := k[X]
abbrev B : Type _ := _root_.FunctionField.ringOfIntegers k F
local instance _p2m_local_instance_ebdac87835_41 : Module.IsTorsionFree (R k) (B k F) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (_root_.FunctionField.ringOfIntegers.algebraMap_injective k F)
open DirectIntegralDifferentialResidue
end QEC.Coding.AlgebraicGeometry.DirectSemilocalDenominator


