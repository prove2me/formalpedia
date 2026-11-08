-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveRelativeCosets
-- name    : QEC_Coding_ExpanderCodes_LPSEffectiveRelativeCosets
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T12:53:38.621219+00:00
-- url     : https://prove2.me/theorems/c1e2163d-f791-472e-a4b9-7fc6ae6e37d9
-- title:
--   LPSEffective Relative Cosets
-- statement:
--   Definitions and structural lemmas for LPSEffective Relative Cosets, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEffectiveRelativeCosets.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHorocyclePoint_im
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHorocyclePoint_im
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
noncomputable def lpsEffectiveRelativeCosetEquiv (N : ℕ) (H : Subgroup SL(2,ℤ))
    (hker : (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict.ker ≤ H) :
    CongruenceSubgroup.Gamma0 N ⧸ H.subgroupOf (CongruenceSubgroup.Gamma0 N) ≃
      lpsEffectiveGamma0 N ⧸
        (H.map (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict).subgroupOf
          (lpsEffectiveGamma0 N) := by
  let φ : SL(2,ℤ) →* lpsEffectiveModularGroup :=
    (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict
  let ψ : CongruenceSubgroup.Gamma0 N →* lpsEffectiveGamma0 N :=
    φ.subgroupMap (CongruenceSubgroup.Gamma0 N)
  let f : CongruenceSubgroup.Gamma0 N ⧸ H.subgroupOf (CongruenceSubgroup.Gamma0 N) →
      lpsEffectiveGamma0 N ⧸ (H.map φ).subgroupOf (lpsEffectiveGamma0 N) :=
    Quotient.map' ψ (by
      intro x y hxy
      rw [QuotientGroup.leftRel_apply] at hxy ⊢
      have hm := Subgroup.mem_map_of_mem φ hxy
      change φ ((x:SL(2,ℤ))⁻¹*y) ∈ H.map φ at hm
      change (φ (x:SL(2,ℤ)))⁻¹*φ (y:SL(2,ℤ)) ∈ H.map φ
      simpa only [map_mul,map_inv] using hm)
  apply Equiv.ofBijective f
  constructor
  · intro x y hxy
    induction x using QuotientGroup.induction_on with | H x =>
      induction y using QuotientGroup.induction_on with | H y =>
        apply Quotient.sound'
        rw [QuotientGroup.leftRel_apply]
        have hxy' : (QuotientGroup.mk (ψ x) :
            lpsEffectiveGamma0 N ⧸ (H.map φ).subgroupOf (lpsEffectiveGamma0 N)) =
              QuotientGroup.mk (ψ y) := hxy
        have hm := QuotientGroup.eq.mp hxy'
        change (φ (x:SL(2,ℤ)))⁻¹*φ (y:SL(2,ℤ)) ∈ H.map φ at hm
        have hh : (x:SL(2,ℤ))⁻¹*y ∈ (H.map φ).comap φ := by
          simpa only [Subgroup.mem_comap,map_mul,map_inv] using hm
        have hc : (H.map φ).comap φ=H := Subgroup.comap_map_eq_self hker
        rw [hc] at hh
        exact hh
  · intro y
    induction y using QuotientGroup.induction_on with | H y =>
      obtain ⟨x,rfl⟩ := φ.subgroupMap_surjective (CongruenceSubgroup.Gamma0 N) y
      exact ⟨QuotientGroup.mk x,rfl⟩
end
end QEC.Coding.TannerLiftedProduct


