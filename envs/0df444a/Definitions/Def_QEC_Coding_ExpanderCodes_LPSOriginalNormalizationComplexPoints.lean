-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationComplexPoints
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalNormalizationComplexPoints
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T08:25:39.696421+00:00
-- url     : https://prove2.me/theorems/b1b5d4af-59f2-4f9d-a28e-f1a3112c41a6
-- title:
--   LPSOriginal Normalization Complex Points
-- statement:
--   Definitions and structural lemmas for LPSOriginal Normalization Complex Points, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNormalizationComplexPoints.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationOverlapEvaluation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGlobalNormalizationComparison
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalizationChart_order_cover

set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms Filter Topology
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local instance _p2m_local_instance_ffe444fe3b_18 : TopologicalSpace (LPSOriginalFilledCurve N) := lpsOriginalFilledTopology N
local instance _p2m_local_instance_ffe444fe3b_19 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local instance _p2m_local_instance_ffe444fe3b_24 : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance _p2m_local_instance_ffe444fe3b_25 : Algebra ℂ K := ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance _p2m_local_instance_ffe444fe3b_26 : IsScalarTower ℂ J K := IsScalarTower.of_algebraMap_eq' rfl
local instance _p2m_local_instance_ffe444fe3b_27 : IsScalarTower ℂ P K := IsScalarTower.of_algebraMap_eq' rfl
def lpsOriginalZeroNormalizationSpecPoint (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)) :
    Spec (.of ℂ) ⟶ lpsOriginalComplexNormalSchemeChart N hpos false :=
  Spec.map (CommRingCat.ofHom (lpsOriginalZeroNormalChartEvaluation N hpos hN x hj))
def lpsOriginalInfinityNormalizationSpecPoint (x : LPSOriginalFilledCurve N)
    (hi : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹) :
    Spec (.of ℂ) ⟶ lpsOriginalComplexNormalSchemeChart N hpos true :=
  Spec.map (CommRingCat.ofHom (lpsOriginalInfinityNormalChartEvaluation N hpos hN x hi))
def lpsOriginalLaurentNormalizationSpecPoint (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X))
    (hi : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹) :
    Spec (.of ℂ) ⟶ Spec (.of (lpsOriginalComplexNormalLaurentChart N hpos)) :=
  Spec.map (CommRingCat.ofHom (lpsOriginalLaurentNormalChartEvaluation N hpos hN x hj hi))
def lpsOriginalNormalizationCurveSpecPoint (x : LPSOriginalFilledCurve N) :
    Spec (.of ℂ) ⟶ lpsOriginalComplexNormalGluedScheme N hpos := by
  classical
  exact if hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X) then
    lpsOriginalZeroNormalizationSpecPoint N hpos hN x hj ≫
      lpsOriginalComplexNormalGluedChartMap N hpos false
  else
    lpsOriginalInfinityNormalizationSpecPoint N hpos hN x
      ((lpsOriginalNormalizationChart_order_cover N hpos hN x).resolve_left hj) ≫
        lpsOriginalComplexNormalGluedChartMap N hpos true
def lpsOriginalNormalizationIntegerBaseChangeSpecPoint (x : LPSOriginalFilledCurve N) :
    Spec (.of ℂ) ⟶ lpsOriginalIntegerNormalComplexBaseChange N hpos :=
  lpsOriginalNormalizationCurveSpecPoint N hpos hN x ≫
    (lpsOriginalComplexNormalGluedIntegerBaseChangeIso N hpos).hom
end
end QEC.Coding.TannerLiftedProduct


