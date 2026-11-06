-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Inverse_DifferentialTraceTransport
-- name    : QEC_Coding_AlgebraicGeometry_Residues_Inverse_DifferentialTraceTransport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:37:35.344204+00:00
-- url     : https://prove2.me/theorems/84413f9f-b6ec-4722-bec8-3cac57c9646b
-- title:
--   Differential Trace Transport
-- statement:
--   Definitions and structural lemmas for Differential Trace Transport, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Inverse/DifferentialTraceTransport.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_InvolutionResidueTransport
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_one
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_add
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_one


set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.InverseDifferentialTraceTransport
open scoped Polynomial RatFunc
open FunctionFieldDifferential
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [oldPolynomialAlgebra : Algebra k[X] F]
variable [oldRationalAlgebra : Algebra k⟮X⟯ F]
variable [oldScalarTower : IsScalarTower k[X] k⟮X⟯ F]
variable [oldFunctionField : _root_.FunctionField k F]
variable [oldSeparable : Algebra.IsSeparable k⟮X⟯ F]
noncomputable local instance directConstantAlgebra : Algebra k F :=
  AffinePlace.constantAlgebra k F
noncomputable local instance directConstantScalarTower :
    IsScalarTower k k⟮X⟯ F :=
  IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap k[X] F (Polynomial.C c) =
      algebraMap k⟮X⟯ F (algebraMap k k⟮X⟯ c)
    simpa only [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C] using
      (IsScalarTower.algebraMap_apply k[X] k⟮X⟯ F (Polynomial.C c))
local notation3 "inverseRationalAlgebra" =>
  InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := oldRationalAlgebra) k F
local notation3 "inverseFunctionField" =>
  InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := oldRationalAlgebra)
    (oldFunctionField := oldFunctionField) k F
local notation3 "inverseIsSeparable" =>
  InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := oldRationalAlgebra)
    (oldSeparable := oldSeparable) k F
@[reducible]
noncomputable def inverseConstantScalarTower :
    letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
    IsScalarTower k k⟮X⟯ F := by
  letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro c
  calc
    algebraMap k F c =
        (@algebraMap k⟮X⟯ F _ _ oldRationalAlgebra)
          (algebraMap k k⟮X⟯ c) :=
      by
        change (@algebraMap k[X] F _ _ oldPolynomialAlgebra) (Polynomial.C c) =
          (@algebraMap k⟮X⟯ F _ _ oldRationalAlgebra)
            (algebraMap k k⟮X⟯ c)
        simpa only [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C] using
          (@IsScalarTower.algebraMap_apply k[X] k⟮X⟯ F _ _ _
            (inferInstance : Algebra k[X] k⟮X⟯) oldRationalAlgebra
            oldPolynomialAlgebra oldScalarTower (Polynomial.C c))
    _ = algebraMap k⟮X⟯ F (algebraMap k k⟮X⟯ c) := by
      change (@algebraMap k⟮X⟯ F _ _ oldRationalAlgebra)
          (algebraMap k k⟮X⟯ c) =
        (@algebraMap k⟮X⟯ F _ _ oldRationalAlgebra)
          (InverseAffinePlace.rationalInvolution k
            (algebraMap k k⟮X⟯ c))
      rw [(InverseAffinePlace.rationalInvolution k).commutes]
end QEC.Coding.AlgebraicGeometry.InverseDifferentialTraceTransport


