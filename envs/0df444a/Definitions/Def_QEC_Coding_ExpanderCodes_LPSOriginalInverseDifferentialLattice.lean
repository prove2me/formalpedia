-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInverseDifferentialLattice
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalInverseDifferentialLattice
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T12:59:48.00505+00:00
-- url     : https://prove2.me/theorems/464c42e5-e6a2-4a98-a4d9-481e1dd85f69
-- title:
--   LPSOriginal Inverse Differential Lattice
-- statement:
--   Definitions and structural lemmas for LPSOriginal Inverse Differential Lattice, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalInverseDifferentialLattice.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalChartComparison
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInversePolynomialMap_eq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.TannerLiftedProduct
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N)
local notation "P" => Polynomial ℂ
local notation "J" => FractionRing P
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "R" => lpsOriginalComplexNormalInfinityChart N hpos
attribute [local instance]
  LPSOriginalLocalKaehlerFinitenessDictionary027
  LPSOriginalLocalKaehlerFinitenessDictionary029
  LPSOriginalLocalKaehlerFinitenessDictionary031
  LPSOriginalLocalKaehlerFinitenessDictionary032
  LPSOriginalLocalKaehlerFinitenessDictionary033
  LPSOriginalLocalKaehlerFinitenessDictionary034
  LPSOriginalLocalKaehlerFinitenessDictionary035
  LPSOriginalLocalKaehlerFinitenessDictionary036
  LPSOriginalLocalKaehlerFinitenessDictionary037
  LPSOriginalLocalKaehlerFinitenessDictionary038
  LPSOriginalLocalKaehlerFinitenessDictionary039
  LPSOriginalLocalKaehlerFinitenessDictionary040
  LPSOriginalLocalKaehlerFinitenessDictionary041
  LPSOriginalLocalKaehlerFinitenessDictionary042
  LPSOriginalLocalKaehlerFinitenessDictionary043
local instance _p2m_local_instance_402e0474f5_41 : Algebra P J := lpsOriginalReciprocalBaseCAlgebra
local instance _p2m_local_instance_402e0474f5_42 : SMul P J := Algebra.toSMul
local instance _p2m_local_instance_402e0474f5_43 : Module P J := Algebra.toModule
local instance _p2m_local_instance_402e0474f5_44 : IsFractionRing P J := lpsOriginalReciprocalBaseC_isFractionRing
local instance _p2m_local_instance_402e0474f5_45 : Algebra P K := (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos).toAlgebra
local instance _p2m_local_instance_402e0474f5_46 : SMul P K := Algebra.toSMul
local instance _p2m_local_instance_402e0474f5_47 : Module P K := Algebra.toModule
local instance _p2m_local_instance_402e0474f5_48 : IsScalarTower P J K := .of_algebraMap_eq' rfl
local instance _p2m_local_instance_402e0474f5_49 : IsScalarTower ℂ P K := .of_algebraMap_eq fun c => by
  change algebraMap J K (algebraMap ℂ J c) =
    algebraMap J K (lpsOriginalComplexJFractionInversion (algebraMap ℂ J c))
  rw [lpsOriginalComplexJFractionInversion_constant]
local instance _p2m_local_instance_402e0474f5_54 : SMulCommClass ℂ P R where
  smul_comm c p r := by simp only [Algebra.smul_def]; ring
local instance _p2m_local_instance_402e0474f5_56 : SMul P (KaehlerDifferential ℂ R) :=
  instSMulKaehlerDifferentialOfSMulCommClass ℂ R
local instance _p2m_local_instance_402e0474f5_58 : Module P (KaehlerDifferential ℂ R) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℂ R
local instance _p2m_local_instance_402e0474f5_60 : SMul R (KaehlerDifferential ℂ R) :=
  LPSOriginalLocalKaehlerFinitenessDictionary035 N hpos
local instance _p2m_local_instance_402e0474f5_62 : Module R (KaehlerDifferential ℂ R) :=
  LPSOriginalLocalKaehlerFinitenessDictionary036 N hpos
local instance _p2m_local_instance_402e0474f5_64 : MulAction R (KaehlerDifferential ℂ R) :=
  (LPSOriginalLocalKaehlerFinitenessDictionary036 N hpos).toMulAction
local instance _p2m_local_instance_402e0474f5_66 : IsScalarTower P R (KaehlerDifferential ℂ R) :=
  KaehlerDifferential.isScalarTower_of_tower («R» := ℂ) (S := R) (R₁ := P) (R₂ := R)
end
end QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.TannerLiftedProduct
open scoped Polynomial RatFunc
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N)
local notation "P" => Polynomial ℂ
local notation "J" => FractionRing P
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "R" => lpsOriginalComplexNormalInfinityChart N hpos
attribute [local instance]
  LPSOriginalLocalKaehlerFinitenessDictionary027
  LPSOriginalLocalKaehlerFinitenessDictionary029
  LPSOriginalLocalKaehlerFinitenessDictionary031
  LPSOriginalLocalKaehlerFinitenessDictionary032
  LPSOriginalLocalKaehlerFinitenessDictionary033
  LPSOriginalLocalKaehlerFinitenessDictionary034
  LPSOriginalLocalKaehlerFinitenessDictionary035
  LPSOriginalLocalKaehlerFinitenessDictionary036
  LPSOriginalLocalKaehlerFinitenessDictionary037
  LPSOriginalLocalKaehlerFinitenessDictionary038
  LPSOriginalLocalKaehlerFinitenessDictionary039
  LPSOriginalLocalKaehlerFinitenessDictionary040
@[reducible] def lpsOriginalInfinityPolynomialAlgebra : Algebra P R := by
  let : Algebra P K := (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos).toAlgebra
  exact inferInstance
local instance _p2m_local_instance_402e0474f5_106 : Algebra P R := lpsOriginalInfinityPolynomialAlgebra N hpos
local instance _p2m_local_instance_402e0474f5_107 : Algebra (RatFunc ℂ) K :=
  InverseAffinePlace.transportedRationalAlgebra (k := ℂ) (F := K)
    (oldRationalAlgebra := lpsOriginalRatFuncAlgebra N hpos)
local instance _p2m_local_instance_402e0474f5_110 : Algebra P K :=
  InverseAffinePlace.transportedPolynomialAlgebra (k := ℂ) (F := K)
    (oldRationalAlgebra := lpsOriginalRatFuncAlgebra N hpos)
local instance _p2m_local_instance_402e0474f5_113 : SMul P K := Algebra.toSMul
local instance _p2m_local_instance_402e0474f5_114 : Module P K := Algebra.toModule
local instance _p2m_local_instance_402e0474f5_116 : SMulCommClass ℂ P R where
  smul_comm c p r := by simp only [Algebra.smul_def]; ring
local instance _p2m_local_instance_402e0474f5_118 : SMul P (KaehlerDifferential ℂ R) :=
  instSMulKaehlerDifferentialOfSMulCommClass ℂ R
local instance _p2m_local_instance_402e0474f5_120 : Module P (KaehlerDifferential ℂ R) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℂ R
local instance _p2m_local_instance_402e0474f5_122 : SMulCommClass ℂ K K where
  smul_comm c f g := by simp only [Algebra.smul_def]; ring
local instance _p2m_local_instance_402e0474f5_124 : SMul K (KaehlerDifferential ℂ K) :=
  instSMulKaehlerDifferentialOfSMulCommClass ℂ K
local instance lpsOriginalTransportedInverseOmegaKModule : Module K (KaehlerDifferential ℂ K) :=
  instModuleKaehlerDifferentialOfSMulCommClass ℂ K
local instance _p2m_local_instance_402e0474f5_129 : SMul R (KaehlerDifferential ℂ R) :=
  LPSOriginalLocalKaehlerFinitenessDictionary035 N hpos
local instance _p2m_local_instance_402e0474f5_131 : Module R (KaehlerDifferential ℂ R) :=
  LPSOriginalLocalKaehlerFinitenessDictionary036 N hpos
local instance _p2m_local_instance_402e0474f5_133 : MulAction R (KaehlerDifferential ℂ R) :=
  (LPSOriginalLocalKaehlerFinitenessDictionary036 N hpos).toMulAction
local instance _p2m_local_instance_402e0474f5_136 : MulAction K (KaehlerDifferential ℂ K) :=
  (lpsOriginalTransportedInverseOmegaKModule N hpos).toMulAction
local instance _p2m_local_instance_402e0474f5_138 : IsScalarTower R K (KaehlerDifferential ℂ K) :=
  KaehlerDifferential.isScalarTower_of_tower («R» := ℂ) (S := K) (R₁ := R) (R₂ := K)
def lpsOriginalTransportedInverseCoefficientMap : KaehlerDifferential ℂ R →ₗ[P] K where
  toFun := fun eta => lpsOriginalGenericKaehlerCoefficientEquiv N hpos
    (KaehlerDifferential.map ℂ ℂ R K eta)
  map_add' eta theta := by rw [map_add, map_add]
  map_smul' p eta := by
    change lpsOriginalGenericKaehlerCoefficientEquiv N hpos
      (KaehlerDifferential.map ℂ ℂ R K (p • eta)) =
        p • lpsOriginalGenericKaehlerCoefficientEquiv N hpos
          (KaehlerDifferential.map ℂ ℂ R K eta)
    rw [← IsScalarTower.algebraMap_smul R p eta, LinearMap.map_smul]
    rw [← IsScalarTower.algebraMap_smul K (algebraMap P R p)
      (KaehlerDifferential.map ℂ ℂ R K eta), LinearEquiv.map_smul]
    have hcoord : algebraMap R K (algebraMap P R p) =
        lpsOriginalReciprocalComplexFieldPolynomialMap N hpos p := rfl
    rw [hcoord]
    change lpsOriginalReciprocalComplexFieldPolynomialMap N hpos p * _ =
      InverseAffinePlace.transportedPolynomialMap (k := ℂ) (F := K)
        (oldRationalAlgebra := lpsOriginalRatFuncAlgebra N hpos) p * _
    rw [lpsOriginalInversePolynomialMap_eq]
end
end QEC.Coding.TannerLiftedProduct


