-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSChi4Eisenstein
-- name    : QEC_Coding_ExpanderCodes_LPSChi4Eisenstein
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:11:27.059823+00:00
-- url     : https://prove2.me/theorems/587ac4c7-5d78-41f2-8347-60418609a9f4
-- title:
--   LPSChi4 Eisenstein
-- statement:
--   Definitions and structural lemmas for LPSChi4 Eisenstein, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSChi4Eisenstein.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2AffineMatrix_action
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2AffineMatrix_translation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2Affine_cusp_tendsto
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2_real_shift_mdifferentiable
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
noncomputable def lpsChi4E2Character : MulChar (ZMod 4) ℂ :=
  ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)
lemma lpsChi4E2Character_apply (a : ZMod 4) : lpsChi4E2Character a=(ZMod.χ₄ a:ℂ) := rfl
lemma lpsChi4E2Character_sum_zero : (∑ a : Fin 4,lpsChi4E2Character (a.val:ZMod 4))=0 := by
  norm_num [Fin.sum_univ_four,lpsChi4E2Character_apply,ZMod.χ₄_apply]
noncomputable def lpsChi4E2Twist (z : ℍ) : ℂ :=
  (gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))⁻¹*
    ∑ a : Fin 4,lpsChi4E2Character (a.val:ZMod 4)*EisensteinSeries.E2 (((a.val:ℝ)/4) +ᵥ z)
lemma lpsChi4E2Twist_mdifferentiable :
    MDiff (fun z : ℍ => lpsChi4E2Twist z) := by
  classical
  unfold lpsChi4E2Twist
  have h : MDiff (∑ a : Fin 4, lpsChi4E2Character (a.val:ZMod 4) •
    (fun z : ℍ => EisensteinSeries.E2 (((a.val:ℝ)/(4:ℝ)) +ᵥ z))) :=
    MDifferentiable.sum (fun (a : Fin 4) ha =>
      MDifferentiable.const_smul _ (lpsE2_real_shift_mdifferentiable ((a.val:ℝ)/(4:ℝ))))
  have h2 := MDifferentiable.const_smul
    (gaussSum (lpsChi4E2Character) (ZMod.stdAddChar (N:=4)))⁻¹ h
  convert h2 using 1
  ext z
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
noncomputable def lpsChi4E2Dilate (m : ℕ) (hm : 0 < m) (z : ℍ) : ℂ :=
  lpsChi4E2Twist (lpsE2AffineMatrix m hm 0 • z)
lemma lpsChi4E2Dilate_eq (m : ℕ) (hm : 0 < m) :
    lpsChi4E2Dilate m hm = (fun z : ℍ =>
      (gaussSum (lpsChi4E2Character) (ZMod.stdAddChar (N:=4)))⁻¹ *
        ∑ r : Fin 4,lpsChi4E2Character (r.val:ZMod 4)*
          EisensteinSeries.E2 (lpsE2AffineMatrix m hm ((r.val:ℝ)/(4:ℝ)) • z)) := by
  funext z
  simp only [lpsChi4E2Dilate,lpsChi4E2Twist,lpsE2AffineMatrix_translation]
lemma lpsChi4E2Dilate_cusp_tendsto (m : ℕ) (hm : 0 < m)
    (γ : SL(2,ℤ)) :
    Tendsto (lpsChi4E2Dilate m hm ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 ((gaussSum (lpsChi4E2Character) (ZMod.stdAddChar (N:=4)))⁻¹ *
        ∑ r : Fin 4,lpsChi4E2Character (r.val:ZMod 4)*
          (((Int.gcd ((4:ℤ)*(m:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0)
            ((4:ℤ)*γ 1 0):ℕ):ℂ)^2/((4:ℂ)^2*(m:ℂ)^2)))) := by
  classical
  have hs := tendsto_finsetSum Finset.univ (fun (r : Fin 4) hr =>
    (lpsE2Affine_cusp_tendsto m 4 hm (by decide : 0 < 4) (r.val:ℤ) γ).const_mul
      (lpsChi4E2Character (r.val:ZMod 4)))
  have h := hs.const_mul (gaussSum (lpsChi4E2Character) (ZMod.stdAddChar (N:=4)))⁻¹
  have he : (lpsChi4E2Dilate m hm ∣[(2:ℤ)] γ) = (fun z : ℍ =>
      (gaussSum (lpsChi4E2Character) (ZMod.stdAddChar (N:=4)))⁻¹ *
        ∑ r : Fin 4,lpsChi4E2Character (r.val:ZMod 4)*
          (((fun w : ℍ => EisensteinSeries.E2
            (lpsE2AffineMatrix m hm ((r.val:ℝ)/(4:ℝ)) • w)) ∣[(2:ℤ)] γ) z)) := by
    rw [lpsChi4E2Dilate_eq]
    funext z
    simp only [ModularForm.SL_slash_apply]
    rw [mul_assoc,Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    ring
  rw [he]
  simpa only [Int.cast_natCast,Nat.cast_ofNat] using h
lemma lpsChi4E2Dilate_one :
    lpsChi4E2Dilate 1 (by decide)=lpsChi4E2Twist := by
  funext z
  unfold lpsChi4E2Dilate
  congr 1
  apply UpperHalfPlane.ext
  rw [lpsE2AffineMatrix_action]
  simp
lemma lpsChi4E2Twist_cusp_gcd_tendsto (γ : SL(2,ℤ)) :
    Tendsto (lpsChi4E2Twist ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 ((gaussSum (lpsChi4E2Character) (ZMod.stdAddChar (N:=4)))⁻¹ *
        ∑ r : Fin 4,lpsChi4E2Character (r.val:ZMod 4)*
          (((Int.gcd ((4:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0)
            ((4:ℤ)*γ 1 0):ℕ):ℂ)^2/(4:ℂ)^2))) := by
  simpa only [lpsChi4E2Dilate_one,Nat.cast_one,Int.cast_one,mul_one,one_pow] using
    lpsChi4E2Dilate_cusp_tendsto 1 (by decide) γ
lemma lpsChi4E2Twist_slash_gamma0 (γ : SL(2,ℤ))
    (hγ : γ∈CongruenceSubgroup.Gamma0 16) :
    (lpsChi4E2Twist ∣[(2:ℤ)] γ)=lpsChi4E2Twist := by
  classical
  obtain ⟨k,hC⟩ := lpsE2Gamma0_lower_entry 4 γ hγ
  have hAD : (γ 0 0:ZMod 4)*(γ 1 1:ZMod 4)=1 := by
    have hd : γ 0 0*γ 1 1-γ 0 1*γ 1 0=1 := by
      simpa only [Matrix.det_fin_two] using γ.det_coe
    have h : (γ 0 0:ZMod 4)*(γ 1 1:ZMod 4)-(γ 0 1:ZMod 4)*(γ 1 0:ZMod 4)=1 := by
      simpa only [map_sub,map_mul,map_one,Int.coe_castRingHom] using
        congrArg (Int.castRingHom (ZMod 4)) hd
    have hc : (γ 1 0:ZMod 4)=0 := by
      rw [hC]
      push_cast
      have hz : (16:ZMod 4)=0 := by decide
      rw [hz]
      simp
    simpa only [hc,mul_zero,sub_zero] using h
  have hEq : (γ 0 0:ZMod 4)=(γ 1 1:ZMod 4) := by
    have he : ∀ a d : ZMod 4,a*d=1 → a=d := by decide
    exact he _ _ hAD
  ext z
  have hr (r : Fin 4) : EisensteinSeries.E2 (((r.val:ℝ)/4) +ᵥ (γ • z))*
      UpperHalfPlane.denom γ (z:ℂ)^(-(2:ℤ))=
      EisensteinSeries.E2 (((r.val:ℝ)/4) +ᵥ z)-
        (1/(2*riemannZeta 2))*EisensteinSeries.D2 γ z := by
    have ht : (4:ℤ)∣(r.val:ℤ)*γ 1 1-(r.val:ℤ)*γ 0 0 := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp
      push_cast
      rw [hEq]
      ring
    obtain ⟨t,ht⟩ := ht
    simpa only [ModularForm.SL_slash_apply,Int.cast_natCast,Nat.cast_ofNat] using
      lpsE2_real_shift_slash 4 γ k (r.val:ℤ) (r.val:ℤ) t hC ht z
  simp only [ModularForm.SL_slash_apply,lpsChi4E2Twist]
  rw [mul_assoc,Finset.sum_mul]
  simp_rw [mul_assoc,hr,mul_sub]
  rw [Finset.sum_sub_distrib,←Finset.sum_mul,lpsChi4E2Character_sum_zero,
    zero_mul,sub_zero]
lemma lpsChi4E2Twist_bounded_at_cusps (c : OnePoint ℝ) (hc : IsCusp c 𝒮ℒ) :
    OnePoint.IsBoundedAt c lpsChi4E2Twist 2 := by
  apply (OnePoint.isBoundedAt_iff_forall_SL2Z hc).mpr
  intro γ hγ
  exact (lpsChi4E2Twist_cusp_gcd_tendsto γ).isBigO_one ℝ
noncomputable def lpsChi4E2TwistModularForm :
    ModularForm (CongruenceSubgroup.Gamma0 16 : Subgroup (GL (Fin 2) ℝ)) 2 where
  toFun := lpsChi4E2Twist
  slash_action_eq' := by
    intro g hg
    obtain ⟨γ,hγ,rfl⟩ := hg
    simpa [Matrix.SpecialLinearGroup.mapGL,←ModularForm.SL_slash] using
      lpsChi4E2Twist_slash_gamma0 γ hγ
  holo' := lpsChi4E2Twist_mdifferentiable
  bdd_at_cusps' := fun hc => lpsChi4E2Twist_bounded_at_cusps _
    (hc.mono (Subgroup.map_le_range (Matrix.SpecialLinearGroup.mapGL ℝ) _))
end QEC.Coding.TannerLiftedProduct


