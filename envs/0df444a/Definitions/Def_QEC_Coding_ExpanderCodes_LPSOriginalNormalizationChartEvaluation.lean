-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationChartEvaluation
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalNormalizationChartEvaluation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T08:16:45.730458+00:00
-- url     : https://prove2.me/theorems/b5311670-4c9d-444c-a61a-56b21cfaa186
-- title:
--   LPSOriginal Normalization Chart Evaluation
-- statement:
--   Definitions and structural lemmas for LPSOriginal Normalization Chart Evaluation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNormalizationChartEvaluation.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalMeromorphicOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AnalyticGermEvaluation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalComplexNormalCharts
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_nonnegative_of_integral_map
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_nonnegative_polynomial_eval
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldLocalOrder_constant_nonnegative
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldLocalOrder_integral_nonnegative

set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms Filter Topology
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local instance _p2m_local_instance_bb7e6d852b_18 : TopologicalSpace (LPSOriginalFilledCurve N) := lpsOriginalFilledTopology N
local instance _p2m_local_instance_bb7e6d852b_19 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "L" => LPSOriginalCompactMeromorphicGermRing N hN
local notation "IC0" => lpsOriginalComplexNormalZeroChart N hpos
local instance _p2m_local_instance_bb7e6d852b_26 : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance _p2m_local_instance_bb7e6d852b_27 : Algebra ℂ K := ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance _p2m_local_instance_bb7e6d852b_28 : Algebra ℂ L := ((lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict.comp
  (lpsOriginalFilledMeromorphicComplexConstants N hN)).toAlgebra
local instance _p2m_local_instance_bb7e6d852b_30 : IsScalarTower ℂ J K := IsScalarTower.of_algebraMap_eq' rfl
local instance _p2m_local_instance_bb7e6d852b_31 : IsScalarTower ℂ P K := IsScalarTower.of_algebraMap_eq' rfl
def lpsOriginalZeroNormalChartToMeromorphicInteger
    (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)) :
    IC0 →+* (AddValuation.toValuation
      (meromorphicOrderValuation (lpsOriginalLocalChartCenter N hN x))).integer := by
  let φ := (lpsOriginalFieldToLocal N hN hpos x).comp (integralClosure P K).val.toRingHom
  refine φ.codRestrict _ ?_
  intro a
  change 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x a.val
  exact lpsOriginalFieldLocalOrder_integral_nonnegative N hN hpos x hj a
def lpsOriginalZeroNormalChartEvaluation
    (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)) :
    IC0 →+* ℂ :=
  (meromorphicNoPoleEvaluation (lpsOriginalLocalChartCenter N hN x)).comp
    (lpsOriginalZeroNormalChartToMeromorphicInteger N hpos hN x hj)
omit [NeZero N] in
lemma lpsOriginalReciprocalFieldPolynomialMap_eval (p : P) :
    lpsOriginalReciprocalComplexFieldPolynomialMap N hpos p =
      p.eval₂ (algebraMap ℂ K) (algebraMap P K Polynomial.X)⁻¹ := by
  let φ : J →ₐ[ℂ] K := IsScalarTower.toAlgHom ℂ J K
  change algebraMap J K
    (QEC.Coding.OriginalNormalizationComparison.ReciprocalFraction.fractionInverse ℂ
      (algebraMap P J p)) = _
  rw [QEC.Coding.OriginalNormalizationComparison.ReciprocalFraction.fractionInverse_polynomial]
  change φ (p.eval₂ (algebraMap ℂ J) (algebraMap P J Polynomial.X)⁻¹) = _
  rw [Polynomial.algHom_eval₂_algebraMap, map_inv₀]
  rfl
lemma lpsOriginalReciprocalFieldPolynomialMap_order_nonnegative
    (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹)
    (p : P) :
    0 ≤ lpsOriginalFieldLocalOrder N hN hpos x
      (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos p) := by
  rw [lpsOriginalReciprocalFieldPolynomialMap_eval]
  exact nonnegative_polynomial_eval (lpsOriginalFieldLocalOrder N hN hpos x)
    (algebraMap ℂ K) (lpsOriginalFieldLocalOrder_constant_nonnegative N hN hpos x) _ hj p
lemma lpsOriginalInfinityIntegral_order_nonnegative
    (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹)
    (a : lpsOriginalComplexNormalInfinityChart N hpos) :
    0 ≤ lpsOriginalFieldLocalOrder N hN hpos x a.val := by
  have hi : (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos).IsIntegralElem a.val :=
    a.property
  exact nonnegative_of_integral_map (lpsOriginalFieldLocalOrder N hN hpos x)
    (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos)
    (lpsOriginalReciprocalFieldPolynomialMap_order_nonnegative N hpos hN x hj) hi
def lpsOriginalInfinityNormalChartToMeromorphicInteger
    (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹) :
    lpsOriginalComplexNormalInfinityChart N hpos →+*
      (AddValuation.toValuation (meromorphicOrderValuation (lpsOriginalLocalChartCenter N hN x))).integer := by
  letI : Algebra P K := (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos).toAlgebra
  let φ := (lpsOriginalFieldToLocal N hN hpos x).comp (integralClosure P K).val.toRingHom
  refine φ.codRestrict _ ?_
  intro a
  change 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x a.val
  exact lpsOriginalInfinityIntegral_order_nonnegative N hpos hN x hj a
def lpsOriginalInfinityNormalChartEvaluation
    (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹) :
    lpsOriginalComplexNormalInfinityChart N hpos →+* ℂ :=
  (meromorphicNoPoleEvaluation (lpsOriginalLocalChartCenter N hN x)).comp
    (lpsOriginalInfinityNormalChartToMeromorphicInteger N hpos hN x hj)
end
end QEC.Coding.TannerLiftedProduct


