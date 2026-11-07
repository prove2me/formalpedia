-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGenericCompactDifferentialComparison
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalGenericCompactDifferentialComparison
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T05:47:35.860144+00:00
-- url     : https://prove2.me/theorems/d1a9b52d-9708-41e8-935e-a10ce88c82d9
-- title:
--   LPSOriginal Generic Compact Differential Comparison
-- statement:
--   Definitions and structural lemmas for LPSOriginal Generic Compact Differential Comparison, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGenericCompactDifferentialComparison.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGenericDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicDifferentialComparison
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_isManifold
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFullMeromorphicEquiv_apply

set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane Manifold ContDiff TensorProduct
noncomputable section
section CompactGenericDifferential
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local instance _p2m_local_instance_f7e67548a0_28 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "L" => LPSOriginalCompactMeromorphicGermRing N hN
local notation "M" => LPSOriginalMeromorphicGermRing UpperHalfPlane.upperHalfPlaneSet
local instance _p2m_local_instance_f7e67548a0_35 : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance _p2m_local_instance_f7e67548a0_36 : Algebra ℂ K := ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance _p2m_local_instance_f7e67548a0_37 : Algebra ℂ L := ((lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict.comp
  (lpsOriginalFilledMeromorphicComplexConstants N hN)).toAlgebra
lemma lpsOriginalGeneratedCompactMeromorphic_restrict (f : K) :
    (lpsOriginalCompactToRestrictedMeromorphic N hN
      (lpsOriginalGeneratedCompactMeromorphicEquiv N hpos hN f)).val =
        lpsOriginalGenericToMeromorphicGerm N hpos f := by
  change (lpsOriginalCompactRestrictedMeromorphicEquiv N hN
    ((lpsOriginalCompactRestrictedMeromorphicEquiv N hN).symm
      (lpsOriginalGeneratedFullMeromorphicEquiv N hpos hN f))).val = _
  rw [RingEquiv.apply_symm_apply]
  exact lpsOriginalGeneratedFullMeromorphicEquiv_apply N hpos hN f
def lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv : K ≃ₐ[ℂ] L where
  toRingEquiv := lpsOriginalGeneratedCompactMeromorphicEquiv N hpos hN
  commutes' c := by
    apply lpsOriginalCompactToRestrictedMeromorphic_injective N hN
    apply Subtype.ext
    change (lpsOriginalCompactToRestrictedMeromorphic N hN
      (lpsOriginalGeneratedCompactMeromorphicEquiv N hpos hN (algebraMap ℂ K c))).val =
      (lpsOriginalCompactToRestrictedMeromorphic N hN (algebraMap ℂ L c)).val
    rw [lpsOriginalGeneratedCompactMeromorphic_restrict]
    rw [(lpsOriginalGenericToMeromorphicGerm N hpos).commutes]
    change algebraMap ℂ M c =
      (lpsOriginalCompactToRestrictedMeromorphic N hN
        ((lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict
          (lpsOriginalFilledMeromorphicComplexConstants N hN c))).val
    rw [lpsOriginalCompactToRestrictedMeromorphic_apply]
    rfl
local instance _p2m_local_instance_f7e67548a0_70 : IsScalarTower ℂ J K := IsScalarTower.of_algebraMap_eq' rfl
local notation "V" => LPSOriginalFilledMeromorphicCovectorRepresentatives N hN
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
local instance _p2m_local_instance_f7e67548a0_74 : AddCommGroup V := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  exact (lpsOriginalFilledMeromorphicCovectorSubmodule N hN).addCommGroup
def lpsOriginalGenericKaehlerComplexCoefficientEquiv : KaehlerDifferential ℂ K ≃ₗ[ℂ] K :=
  (lpsOriginalGenericKaehlerCoefficientEquiv N hpos).restrictScalars ℂ
def lpsOriginalGenericCompactCoefficientToCovectorEquiv :
    K ≃ₗ[ℂ] LPSOriginalCompactMeromorphicCovectorGerms N hN := by
  let e₂ : K ≃ₗ[ℂ] L :=
    (lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN).toLinearEquiv
  let e₃ : L ≃ₗ[ℂ] LPSOriginalCompactMeromorphicCovectorGerms N hN :=
    (lpsOriginalCompactMeromorphicCovectorLinearEquiv N hN).symm
  exact e₂.trans e₃
def lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv :
    KaehlerDifferential ℂ K ≃ₗ[ℂ] LPSOriginalCompactMeromorphicCovectorGerms N hN :=
  (lpsOriginalGenericKaehlerComplexCoefficientEquiv N hpos).trans
    (lpsOriginalGenericCompactCoefficientToCovectorEquiv N hpos hN)
end CompactGenericDifferential
end
end QEC.Coding.TannerLiftedProduct


