-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_IntegralDifferentialTraceRegularity
-- name    : QEC_Coding_AlgebraicGeometry_Residues_Direct_IntegralDifferentialTraceRegularity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:42:29.209825+00:00
-- url     : https://prove2.me/theorems/82052104-c8bb-49c0-b932-7efa69db60bf
-- title:
--   Integral Differential Trace Regularity
-- statement:
--   Definitions and structural lemmas for Integral Differential Trace Regularity, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/IntegralDifferentialTraceRegularity.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SmithDifferentialTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicIdealResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywisePolynomialDerivative_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicPolynomialDifferential
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicIdealResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_add
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_one
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywisePolynomialDerivative_apply


set_option autoImplicit false
open scoped Polynomial RatFunc nonZeroDivisors
namespace QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialTraceRegularity
open QEC.Coding.AlgebraicGeometry
open FunctionFieldDifferential
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra (RatFunc k) F]
variable [IsScalarTower k[X] (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
noncomputable local instance integralDifferentialTraceRegularity_constantAlgebra : Algebra k F := AffinePlace.constantAlgebra k F
attribute [local instance] integralDifferentialTraceRegularity_constantAlgebra
noncomputable local instance integralDifferentialTraceRegularity_scalarTower : IsScalarTower k (RatFunc k) F :=
  IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap k[X] F (Polynomial.C c) =
      algebraMap (RatFunc k) F (algebraMap k (RatFunc k) c)
    simpa only [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C] using
      (IsScalarTower.algebraMap_apply k[X] (RatFunc k) F (Polynomial.C c))
attribute [local instance] integralDifferentialTraceRegularity_scalarTower
abbrev R : Type _ := k[X]
abbrev B : Type _ := _root_.FunctionField.ringOfIntegers k F
local instance _p2m_local_instance_828a280e13_54 : Module.IsTorsionFree (R k) (B k F) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (_root_.FunctionField.ringOfIntegers.algebraMap_injective k F)
local instance _p2m_local_instance_828a280e13_58 : Module.Finite (R k) (B k F) :=
  AffinePlace.finite_ringOfIntegers k F
local instance _p2m_local_instance_828a280e13_61 : IsLocalization
    (Algebra.algebraMapSubmonoid (B k F) (R k)⁰) F :=
  IsIntegralClosure.isLocalization_of_isSeparable
    (R k) (RatFunc k) F (B k F)
noncomputable def directIntegralDifferentialTracePolynomial
    (b t : B k F) : R k := by
  let basis := Module.finBasis (R k) (B k F)
  exact Matrix.trace
    (LinearMap.toMatrix basis basis (Algebra.lmul (R k) (B k F) b) *
      entrywisePolynomialDerivative
        (LinearMap.toMatrix basis basis (Algebra.lmul (R k) (B k F) t)))
end QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialTraceRegularity


