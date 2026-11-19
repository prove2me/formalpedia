-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaModularForm
-- name    : QEC_Coding_ExpanderCodes_LPSThetaModularForm
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:33:14.707205+00:00
-- url     : https://prove2.me/theorems/87c90db6-5d2f-4674-a04b-8466e3e37169
-- title:
--   LPSTheta Modular Form
-- statement:
--   Definitions and structural lemmas for LPSTheta Modular Form, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaModularForm.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaGaussFourthReduction
import Mathlib.NumberTheory.ModularForms.Basic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0_pos_lower_dvd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsStandardTheta_isBoundedAtImInfty_slash
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsStandardTheta_slash_gamma0_scalar
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaPositiveGaussScalar_eq_fourth
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_fourth
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex Real
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
lemma lpsThetaPositiveGaussScalar_eq_one (q : ℕ) (hq : 0 < q)
    (γ : SL(2,ℤ)) (hc : 0 < γ 1 0) (hlevel : 16*q^2 ∣ (γ 1 0).toNat) :
    lpsThetaPositiveGaussScalar q γ = 1 := by
  let c := (γ 1 0).toNat
  have hcp : 0 < c := by omega
  let : NeZero c := ⟨ne_of_gt hcp⟩
  have hci : (c:ℤ)=γ 1 0 := Int.toNat_of_nonneg hc.le
  have hdet : γ 0 0*γ 1 1-γ 0 1*(c:ℤ)=1 := by
    rw [hci]
    simpa only [Matrix.det_fin_two] using γ.det_coe
  have hunit : IsUnit (γ 0 0:ZMod c) := by
    apply IsUnit.of_mul_eq_one (γ 1 1:ZMod c)
    have h := congrArg (fun x : ℤ => (x:ZMod c)) hdet
    simpa using h
  have h4 : 4 ∣ c := dvd_trans (show 4 ∣ 16*q^2 from ⟨4*q^2,by ring⟩) hlevel
  rw [lpsThetaPositiveGaussScalar_eq_fourth q hq γ hc hlevel,
    lpsUnaryQuadraticGauss_fourth c h4 (γ 0 0) hunit]
  have hcC : (c:ℂ)≠0 := by exact_mod_cast ne_of_gt hcp
  change -(4*(c:ℂ)^2)⁻¹ * (-4*(c:ℂ)^2) = 1
  field_simp [hcC]
lemma lpsThetaGammaGaussScalar_eq_one (q : ℕ) (hq : 0 < q) (γ : SL(2,ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 (16*q^2)) :
    lpsThetaGammaGaussScalar q γ = 1 := by
  rcases lt_trichotomy (γ 1 0) 0 with hn | hz | hp
  · have hpos : 0 < (-γ) 1 0 := by simpa using neg_pos.mpr hn
    have hγn : (-γ) ∈ CongruenceSubgroup.Gamma0 (16*q^2) := by
      rw [CongruenceSubgroup.Gamma0_mem] at hγ ⊢
      simpa using congrArg Neg.neg hγ
    simpa only [lpsThetaGammaGaussScalar,if_neg (ne_of_lt hn),
      if_neg (not_lt_of_ge hn.le)] using lpsThetaPositiveGaussScalar_eq_one q hq (-γ) hpos
        (lpsGamma0_pos_lower_dvd _ _ hγn hpos)
  · simp [lpsThetaGammaGaussScalar,hz]
  · simpa only [lpsThetaGammaGaussScalar,if_neg (ne_of_gt hp),if_pos hp] using
      lpsThetaPositiveGaussScalar_eq_one q hq γ hp (lpsGamma0_pos_lower_dvd _ _ hγ hp)
lemma lpsStandardTheta_slash_gamma0 (q : ℕ) (hq : 0 < q) (γ : SL(2,ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 (16*q^2)) :
    (fun w : UpperHalfPlane => lpsStandardTheta q w) ∣[(2:ℤ)] γ =
      (fun w : UpperHalfPlane => lpsStandardTheta q w) := by
  funext z
  rw [lpsStandardTheta_slash_gamma0_scalar q hq γ hγ z,
    lpsThetaGammaGaussScalar_eq_one q hq γ hγ,one_mul]
lemma lpsStandardTheta_mdifferentiable (q : ℕ) (hq : 0<q) :
    MDiff (fun z : ℍ => lpsStandardTheta q z) := by
  intro z
  exact (differentiableAt_lpsStandardTheta q hq z.2).mdifferentiableAt.comp
    z z.mdifferentiable_coe
lemma lpsStandardTheta_bounded_at_cusps (q : ℕ) (hq : 0<q)
    {c : OnePoint ℝ} (hc : IsCusp c
      (CongruenceSubgroup.Gamma0 (16*q^2) : Subgroup (GL (Fin 2) ℝ))) :
    c.IsBoundedAt (fun z : ℍ => lpsStandardTheta q z) (2:ℤ) := by
  have hcSL : IsCusp c 𝒮ℒ := hc.mono
    (Subgroup.map_le_range (Matrix.SpecialLinearGroup.mapGL ℝ) _)
  obtain ⟨γ,rfl⟩ := isCusp_SL2Z_iff'.mp hcSL
  rw [OnePoint.IsBoundedAt.smul_iff,OnePoint.isBoundedAt_infty_iff]
  simpa [Matrix.SpecialLinearGroup.mapGL, ← ModularForm.SL_slash] using
    lpsStandardTheta_isBoundedAtImInfty_slash q hq γ
noncomputable def lpsStandardThetaModularForm (q : ℕ) (hq : 0<q) :
    ModularForm (CongruenceSubgroup.Gamma0 (16*q^2) : Subgroup (GL (Fin 2) ℝ)) (2:ℤ) where
  toFun := fun z => lpsStandardTheta q z
  slash_action_eq' := by
    intro g hg
    obtain ⟨γ,hγ,rfl⟩ := hg
    simpa [Matrix.SpecialLinearGroup.mapGL, ← ModularForm.SL_slash] using
      lpsStandardTheta_slash_gamma0 q hq γ hγ
  holo' := lpsStandardTheta_mdifferentiable q hq
  bdd_at_cusps' := lpsStandardTheta_bounded_at_cusps q hq
end QEC.Coding.TannerLiftedProduct


