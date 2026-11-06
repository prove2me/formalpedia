-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Inverse_SimplePoleTraceResidue
-- name    : QEC_Coding_AlgebraicGeometry_Residues_Inverse_SimplePoleTraceResidue
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:51:59.774959+00:00
-- url     : https://prove2.me/theorems/504d6d56-4bac-43d5-b40a-de825f910811
-- title:
--   Simple Pole Trace Residue
-- statement:
--   Definitions and structural lemmas for Simple Pole Trace Residue, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Inverse/SimplePoleTraceResidue.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SimplePoleTraceResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Inverse_DifferentialTraceTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Inverse_FibreDirectFactor
import Theorems.Thm_Ideal_Factors_quotientResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorResidueTransport_directFactorResidueEquiv_algebraMap
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSmithTraceResidue_directBaseResidueRationalAdicEquiv_quotientResidueEquiv
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
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseFibreDirectFactor_infinityFibreEquivDirectFactors_apply_asIdeal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywisePolynomialDerivative_apply
attribute [local simp] Ideal.Factors.quotientResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicPolynomialDifferential
attribute [local simp] QEC.Coding.AlgebraicGeometry.DirectFactorResidueTransport.directFactorResidueEquiv_algebraMap
attribute [local simp] QEC.Coding.AlgebraicGeometry.DirectFactorSmithTraceResidue.directBaseResidueRationalAdicEquiv_quotientResidueEquiv
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
attribute [local simp] QEC.Coding.AlgebraicGeometry.InverseFibreDirectFactor.infinityFibreEquivDirectFactors_apply_asIdeal
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_add
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_one
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywisePolynomialDerivative_apply


set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.InverseSimplePoleTraceResidue
open scoped Polynomial RatFunc BigOperators
open FunctionFieldDifferential
open UniqueFactorizationMonoid
variable {k : Type*} [Field k] [Finite k]
noncomputable def idealXResidueEquiv :
    (Polynomial.idealX k).asIdeal.ResidueField ≃+* k :=
  (Ideal.Factors.quotientResidueEquiv
      (Polynomial.idealX k).asIdeal).symm.trans
    ((Ideal.quotEquivOfEq (by
        rw [Polynomial.idealX_span]
        simp)).trans
      (Polynomial.quotientSpanXSubCAlgEquiv (0 : k)).toRingEquiv)
section DirectFactor
variable {F : Type*} [Field F]
variable [Algebra k[X] F] [Algebra (RatFunc k) F]
variable [IsScalarTower k[X] (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
noncomputable local instance infinityDirectConstantAlgebra : Algebra k F :=
  AffinePlace.constantAlgebra k F
attribute [local instance] infinityDirectConstantAlgebra
noncomputable local instance infinityDirectConstantScalarTower :
    IsScalarTower k (RatFunc k) F :=
  IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap k[X] F (Polynomial.C c) =
      algebraMap (RatFunc k) F (algebraMap k (RatFunc k) c)
    simpa only [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C] using
      (IsScalarTower.algebraMap_apply k[X] (RatFunc k) F (Polynomial.C c))
attribute [local instance] infinityDirectConstantScalarTower
noncomputable abbrev B (k F : Type*) [Field k] [Field F] [Algebra k[X] F]
    [Algebra (RatFunc k) F] [IsScalarTower k[X] (RatFunc k) F]
    [_root_.FunctionField k F] :=
  _root_.FunctionField.ringOfIntegers k F
local instance _p2m_local_instance_9ae6b462cd_402 : Module.IsTorsionFree k[X] (B k F) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (_root_.FunctionField.ringOfIntegers.algebraMap_injective k F)
end DirectFactor
section InfinityFibre
variable {F : Type*} [Field F]
variable [oldPolynomialAlgebra : Algebra k[X] F]
variable [oldRationalAlgebra : Algebra (RatFunc k) F]
variable [oldScalarTower : IsScalarTower k[X] (RatFunc k) F]
variable [oldFunctionField : _root_.FunctionField k F]
variable [oldSeparable : Algebra.IsSeparable (RatFunc k) F]
noncomputable local instance directConstantAlgebra : Algebra k F :=
  AffinePlace.constantAlgebra k F
attribute [local instance] directConstantAlgebra
noncomputable local instance directConstantScalarTower :
    IsScalarTower k (RatFunc k) F :=
  IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap k[X] F (Polynomial.C c) =
      algebraMap (RatFunc k) F (algebraMap k (RatFunc k) c)
    simpa only [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C] using
      (IsScalarTower.algebraMap_apply k[X] (RatFunc k) F (Polynomial.C c))
attribute [local instance] directConstantScalarTower
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
@[reducible] noncomputable def inverseConstantScalarTower :
    letI : Algebra (RatFunc k) F := inverseRationalAlgebra
    IsScalarTower k (RatFunc k) F := by
  letI : Algebra (RatFunc k) F := inverseRationalAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro c
  calc
    algebraMap k F c =
        (@algebraMap (RatFunc k) F _ _ oldRationalAlgebra)
          (algebraMap k (RatFunc k) c) := by
      change (@algebraMap k[X] F _ _ oldPolynomialAlgebra)
          (Polynomial.C c) =
        (@algebraMap (RatFunc k) F _ _ oldRationalAlgebra)
          (algebraMap k (RatFunc k) c)
      simpa only [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C] using
        (@IsScalarTower.algebraMap_apply k[X] (RatFunc k) F _ _ _ _
          oldRationalAlgebra oldPolynomialAlgebra oldScalarTower
          (Polynomial.C c))
    _ = algebraMap (RatFunc k) F (algebraMap k (RatFunc k) c) := by
      change (@algebraMap (RatFunc k) F _ _ oldRationalAlgebra)
          (algebraMap k (RatFunc k) c) =
        (@algebraMap (RatFunc k) F _ _ oldRationalAlgebra)
          (InverseAffinePlace.rationalInvolution k
            (algebraMap k (RatFunc k) c))
      rw [(InverseAffinePlace.rationalInvolution k).commutes]
@[reducible] noncomputable def affineConstantScalarTower :
    letI : Algebra k F := AffinePlace.constantAlgebra k F
    IsScalarTower k (RatFunc k) F := by
  letI : Algebra k F := AffinePlace.constantAlgebra k F
  apply IsScalarTower.of_algebraMap_eq
  intro c
  change algebraMap k[X] F (Polynomial.C c) =
    algebraMap (RatFunc k) F (algebraMap k (RatFunc k) c)
  simpa only [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C] using
    (IsScalarTower.algebraMap_apply k[X] (RatFunc k) F (Polynomial.C c))
abbrev DifferentialAt (A : Algebra k F) : Type _ :=
  @Differential k F _ _ A
abbrev GlobalPlaceAt (A : Algebra k F) : Type _ :=
  @GlobalPlace k F _ _ _ A
def castDifferential {A A' : Algebra k F} (hA : A = A') :
    DifferentialAt A → DifferentialAt A' :=
  cast (congrArg DifferentialAt hA)
def castGlobalPlace {A A' : Algebra k F} (hA : A = A') :
    GlobalPlaceAt A → GlobalPlaceAt A' :=
  cast (congrArg GlobalPlaceAt hA)
noncomputable def functionFieldDifferentialTraceAt
    (A : Algebra k F) (ρ : Algebra (RatFunc k) F)
    (τ : letI : Algebra k F := A
      letI : Algebra (RatFunc k) F := ρ
      IsScalarTower k (RatFunc k) F)
    (σ : letI : Algebra (RatFunc k) F := ρ
      Algebra.IsSeparable (RatFunc k) F)
    (φ : letI : Algebra (RatFunc k) F := ρ
      FiniteDimensional (RatFunc k) F) :
    DifferentialAt A → Differential k (RatFunc k) := by
  letI : Algebra k F := A
  letI : Algebra (RatFunc k) F := ρ
  letI : IsScalarTower k (RatFunc k) F := τ
  letI : Algebra.IsSeparable (RatFunc k) F := σ
  letI : FiniteDimensional (RatFunc k) F := φ
  exact fun omega => functionFieldDifferentialTrace (k := k) (F := F) omega
noncomputable def simplePoleTraceResidueAt
    (A : Algebra k F) (ρ : Algebra (RatFunc k) F)
    (τ : letI : Algebra k F := A
      letI : Algebra (RatFunc k) F := ρ
      IsScalarTower k (RatFunc k) F)
    (σ : letI : Algebra (RatFunc k) F := ρ
      Algebra.IsSeparable (RatFunc k) F)
    (φ : letI : Algebra (RatFunc k) F := ρ
      FiniteDimensional (RatFunc k) F)
    (P : GlobalPlaceAt A) (omega : DifferentialAt A)
    (homega : omega ∈
      @Differential.simplePoleDifferentialLattice k F _ _ _ A P) : k := by
  letI : Algebra k F := A
  letI : Algebra (RatFunc k) F := ρ
  letI : IsScalarTower k (RatFunc k) F := τ
  letI : Algebra.IsSeparable (RatFunc k) F := σ
  letI : FiniteDimensional (RatFunc k) F := φ
  exact Differential.simplePoleTraceResidue (k := k) (F := F)
    P omega homega
end InfinityFibre
end QEC.Coding.AlgebraicGeometry.InverseSimplePoleTraceResidue


