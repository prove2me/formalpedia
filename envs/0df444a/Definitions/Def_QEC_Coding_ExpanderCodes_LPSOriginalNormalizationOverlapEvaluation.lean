-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationOverlapEvaluation
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalNormalizationOverlapEvaluation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T08:19:52.143221+00:00
-- url     : https://prove2.me/theorems/b01ef06b-cde5-4f78-ad13-26e12da24a6f
-- title:
--   LPSOriginal Normalization Overlap Evaluation
-- statement:
--   Definitions and structural lemmas for LPSOriginal Normalization Overlap Evaluation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNormalizationOverlapEvaluation.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationChartEvaluation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_nonnegative_laurent_map
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_nonnegative_of_integral_map
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldLocalOrder_constant_nonnegative

set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms Filter Topology
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local instance _p2m_local_instance_9017904347_15 : TopologicalSpace (LPSOriginalFilledCurve N) := lpsOriginalFilledTopology N
local instance _p2m_local_instance_9017904347_16 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "ICL" => lpsOriginalComplexNormalLaurentChart N hpos
local instance _p2m_local_instance_9017904347_22 : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance _p2m_local_instance_9017904347_23 : Algebra ℂ K := ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance _p2m_local_instance_9017904347_24 : IsScalarTower ℂ J K := IsScalarTower.of_algebraMap_eq' rfl
local instance _p2m_local_instance_9017904347_25 : IsScalarTower ℂ P K := IsScalarTower.of_algebraMap_eq' rfl
omit [NeZero N] in
lemma lpsOriginalLaurentBase_constant (c : ℂ) :
    lpsOriginalComplexLaurentBaseToGeneratedField N hpos (LaurentPolynomial.C c) =
      algebraMap ℂ K c := by
  change algebraMap J K (lpsOriginalComplexLaurentBaseFractionMap (LaurentPolynomial.C c)) = _
  rw [← Polynomial.toLaurent_C, lpsOriginalComplexLaurentBaseFractionMap_polynomial]
  change algebraMap J K (algebraMap P J (Polynomial.C c)) = _
  rw [Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply ℂ P J]
  rfl
omit [NeZero N] in
lemma lpsOriginalLaurentBase_T_one :
    lpsOriginalComplexLaurentBaseToGeneratedField N hpos (LaurentPolynomial.T 1) =
      algebraMap P K Polynomial.X := by
  change algebraMap J K (lpsOriginalComplexLaurentBaseFractionMap (LaurentPolynomial.T 1)) = _
  rw [lpsOriginalComplexLaurentBaseFractionMap_T_one]
  rfl
omit [NeZero N] in
lemma lpsOriginalLaurentBase_T_neg_one :
    lpsOriginalComplexLaurentBaseToGeneratedField N hpos (LaurentPolynomial.T (-1)) =
      (algebraMap P K Polynomial.X)⁻¹ := by
  change algebraMap J K
    (lpsOriginalComplexLaurentBaseFractionMap (LaurentPolynomial.T (-1))) = _
  rw [lpsOriginalComplexLaurentBaseFractionMap_T_neg_one, map_inv₀]
  rfl
lemma lpsOriginalLaurentBase_order_nonnegative
    (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X))
    (hi : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹)
    (p : LaurentPolynomial ℂ) :
    0 ≤ lpsOriginalFieldLocalOrder N hN hpos x
      (lpsOriginalComplexLaurentBaseToGeneratedField N hpos p) := by
  apply nonnegative_laurent_map (lpsOriginalFieldLocalOrder N hN hpos x)
    (lpsOriginalComplexLaurentBaseToGeneratedField N hpos)
  · intro c
    rw [lpsOriginalLaurentBase_constant]
    exact lpsOriginalFieldLocalOrder_constant_nonnegative N hN hpos x c
  · rw [lpsOriginalLaurentBase_T_one]; exact hj
  · rw [lpsOriginalLaurentBase_T_neg_one]; exact hi
lemma lpsOriginalLaurentIntegral_order_nonnegative
    (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X))
    (hi : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹)
    (a : ICL) : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x a.val := by
  have ha : (lpsOriginalComplexLaurentBaseToGeneratedField N hpos).IsIntegralElem a.val :=
    a.property
  exact nonnegative_of_integral_map (lpsOriginalFieldLocalOrder N hN hpos x)
    (lpsOriginalComplexLaurentBaseToGeneratedField N hpos)
    (lpsOriginalLaurentBase_order_nonnegative N hpos hN x hj hi) ha
def lpsOriginalLaurentNormalChartToMeromorphicInteger
    (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X))
    (hi : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹) :
    ICL →+* (AddValuation.toValuation
      (meromorphicOrderValuation (lpsOriginalLocalChartCenter N hN x))).integer := by
  letI : Algebra (LaurentPolynomial ℂ) K :=
    (lpsOriginalComplexLaurentBaseToGeneratedField N hpos).toAlgebra
  let φ := (lpsOriginalFieldToLocal N hN hpos x).comp
    (integralClosure (LaurentPolynomial ℂ) K).val.toRingHom
  refine φ.codRestrict _ ?_
  intro a
  change 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x a.val
  exact lpsOriginalLaurentIntegral_order_nonnegative N hpos hN x hj hi a
def lpsOriginalLaurentNormalChartEvaluation
    (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X))
    (hi : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹) : ICL →+* ℂ :=
  (meromorphicNoPoleEvaluation (lpsOriginalLocalChartCenter N hN x)).comp
    (lpsOriginalLaurentNormalChartToMeromorphicInteger N hpos hN x hj hi)
end
end QEC.Coding.TannerLiftedProduct


