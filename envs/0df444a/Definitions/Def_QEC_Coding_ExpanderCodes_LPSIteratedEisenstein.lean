-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSIteratedEisenstein
-- name    : QEC_Coding_ExpanderCodes_LPSIteratedEisenstein
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:12:19.768518+00:00
-- url     : https://prove2.me/theorems/1c1be12c-7e4e-45ab-b51c-5d6f9a337ae4
-- title:
--   LPSIterated Eisenstein
-- statement:
--   Definitions and structural lemmas for LPSIterated Eisenstein, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIteratedEisenstein.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSChi4Eisenstein
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2AffineMatrix_action
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2Affine_cusp_tendsto
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2RealTranslation_action
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Twist_mdifferentiable
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
noncomputable def lpsChi4PrimeE2Twist (q : ℕ) [Fact q.Prime] (z : ℍ) : ℂ :=
  (gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))⁻¹ *
    ∑ r : Fin 4,lpsChi4E2Character (r.val:ZMod 4)*
      lpsQuadraticE2Twist q (((r.val:ℝ)/4) +ᵥ z)
lemma lpsFunction_real_shift_mdifferentiable (f : ℍ→ℂ) (hf : MDiff f) (r : ℝ) :
    MDiff (fun z : ℍ => f (r +ᵥ z)) := by
  have hp : 0<(Matrix.SpecialLinearGroup.mapGL ℝ (lpsE2RealTranslation r)).det.val := by simp
  have h := hf.comp (UpperHalfPlane.mdifferentiable_smul hp)
  have he : (fun z : ℍ => f (Matrix.SpecialLinearGroup.mapGL ℝ (lpsE2RealTranslation r) • z))=
      (fun z : ℍ => f (r +ᵥ z)) := by
    funext z
    apply congrArg f
    change lpsE2RealTranslation r • z=r +ᵥ z
    exact lpsE2RealTranslation_action r z
  change MDiff (fun z : ℍ => f (Matrix.SpecialLinearGroup.mapGL ℝ (lpsE2RealTranslation r) • z)) at h
  rw [he] at h
  exact h
lemma lpsChi4PrimeE2Twist_mdifferentiable (q : ℕ) [Fact q.Prime] : MDiff (lpsChi4PrimeE2Twist q) := by
  classical
  unfold lpsChi4PrimeE2Twist
  have h : MDiff (∑ r : Fin 4,lpsChi4E2Character (r.val:ZMod 4) •
      (fun z : ℍ => lpsQuadraticE2Twist q (((r.val:ℝ)/4) +ᵥ z))) :=
    MDifferentiable.sum (fun (r : Fin 4) hr =>
      MDifferentiable.const_smul _ (lpsFunction_real_shift_mdifferentiable _
        (lpsQuadraticE2Twist_mdifferentiable q) ((r.val:ℝ)/4)))
  have h2 := MDifferentiable.const_smul
    (gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))⁻¹ h
  have he : ((gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))⁻¹ •
      (∑ r : Fin 4,lpsChi4E2Character (r.val:ZMod 4) •
        (fun z : ℍ => lpsQuadraticE2Twist q (((r.val:ℝ)/4) +ᵥ z))))=
      (fun z : ℍ => (gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))⁻¹ *
        ∑ r : Fin 4,lpsChi4E2Character (r.val:ZMod 4)*lpsQuadraticE2Twist q (((r.val:ℝ)/4) +ᵥ z)) := by
    funext z
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [he] at h2
  exact h2
lemma lpsE2ShiftConjugate_actual_denom (N : ℕ) [NeZero N] (γ δ : SL(2,ℤ)) (k s : ℤ)
    (hC : γ 1 0=(N:ℤ)^2*k) (h10 : δ 1 0=(N:ℤ)^2*k)
    (h11 : δ 1 1=γ 1 1-s*(N:ℤ)*k) (z : ℍ) :
    UpperHalfPlane.denom δ ((((s:ℝ)/(N:ℝ)) +ᵥ z:ℍ):ℂ)=UpperHalfPlane.denom γ (z:ℂ) := by
  have hN : (N:ℂ)≠0 := by exact_mod_cast NeZero.ne N
  rw [ModularGroup.denom_apply,ModularGroup.denom_apply]
  simp only [UpperHalfPlane.coe_vadd,Complex.ofReal_div,Complex.ofReal_intCast,Complex.ofReal_natCast]
  rw [h10,h11,hC]
  push_cast
  rw [show (s:ℂ)/(N:ℂ)+(z:ℂ)=(z:ℂ)+(s:ℂ)/(N:ℂ) by ring]
  exact lpsE2ShiftConjugate_denom (N:ℂ) (k:ℂ) (s:ℂ) (γ 1 1:ℂ) (z:ℂ) hN
lemma lpsChi4PrimeE2Shift_slash (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (γ : SL(2,ℤ)) (k r t : ℤ) (hC : γ 1 0=(4:ℤ)^2*((q:ℤ)^2*k))
    (hrs : r*γ 1 1-r*γ 0 0=(4:ℤ)*t) (z : ℍ) :
    (((fun w : ℍ => lpsQuadraticE2Twist q (((r:ℝ)/4) +ᵥ w)) ∣[(2:ℤ)] γ) z)=
      lpsQuadraticE2Twist q (((r:ℝ)/4) +ᵥ z) := by
  let δ := lpsE2ShiftConjugate 4 γ ((q:ℤ)^2*k) r r t hC hrs
  have hδ : δ∈CongruenceSubgroup.Gamma0 (q^2) := by
    rw [CongruenceSubgroup.Gamma0_mem]
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (δ 1 0) (q^2)).mpr
    refine ⟨16*k,?_⟩
    change (4:ℤ)^2*((q:ℤ)^2*k)=(q^2:ℕ)*(16*k)
    push_cast
    ring
  have ha := lpsE2ShiftConjugate_action 4 γ δ ((q:ℤ)^2*k) r r t hC hrs rfl rfl rfl rfl z
  have hd := lpsE2ShiftConjugate_actual_denom 4 γ δ ((q:ℤ)^2*k) r hC rfl rfl z
  norm_num only [Nat.cast_ofNat] at hd
  have h := congrFun (lpsQuadraticE2Twist_slash_gamma0 q hq2 δ hδ) (((r:ℝ)/4) +ᵥ z)
  simp only [ModularForm.SL_slash_apply] at h ⊢
  norm_num only [Nat.cast_ofNat] at ha
  rw [ha,hd] at h
  exact h
lemma lpsChi4PrimeE2Twist_slash_gamma0 (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 ((4*q)^2)) :
    (lpsChi4PrimeE2Twist q ∣[(2:ℤ)] γ)=lpsChi4PrimeE2Twist q := by
  classical
  obtain ⟨k,hC⟩ := lpsE2Gamma0_lower_entry (4*q) γ hγ
  have hC4 : γ 1 0=(4:ℤ)^2*((q:ℤ)^2*k) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat,mul_pow,mul_assoc] using hC
  have hAD : (γ 0 0:ZMod 4)*(γ 1 1:ZMod 4)=1 := by
    have hd : γ 0 0*γ 1 1-γ 0 1*γ 1 0=1 := by
      simpa only [Matrix.det_fin_two] using γ.det_coe
    have h : (γ 0 0:ZMod 4)*(γ 1 1:ZMod 4)-(γ 0 1:ZMod 4)*(γ 1 0:ZMod 4)=1 := by
      simpa only [map_sub,map_mul,map_one,Int.coe_castRingHom] using congrArg (Int.castRingHom (ZMod 4)) hd
    have hc : (γ 1 0:ZMod 4)=0 := by
      rw [hC4]
      push_cast
      have hz : (16:ZMod 4)=0 := by decide
      rw [hz]
      simp
    simpa only [hc,mul_zero,sub_zero] using h
  have hEq : (γ 0 0:ZMod 4)=(γ 1 1:ZMod 4) := by
    have he : ∀ a d : ZMod 4,a*d=1 → a=d := by decide
    exact he _ _ hAD
  ext z
  have hr (r : Fin 4) : lpsQuadraticE2Twist q (((r.val:ℝ)/4) +ᵥ (γ • z))*
      UpperHalfPlane.denom γ (z:ℂ)^(-(2:ℤ))=lpsQuadraticE2Twist q (((r.val:ℝ)/4) +ᵥ z) := by
    have ht : (4:ℤ)∣(r.val:ℤ)*γ 1 1-(r.val:ℤ)*γ 0 0 := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp
      push_cast
      rw [hEq]
      ring
    obtain ⟨t,ht⟩ := ht
    simpa only [ModularForm.SL_slash_apply,Int.cast_natCast] using
      lpsChi4PrimeE2Shift_slash q hq2 γ k (r.val:ℤ) t hC4 ht z
  simp only [ModularForm.SL_slash_apply,lpsChi4PrimeE2Twist]
  rw [mul_assoc,Finset.sum_mul]
  simp_rw [mul_assoc,hr]
noncomputable def lpsChi4PrimeE2Dilate (q m : ℕ) [Fact q.Prime] (hm : 0 < m) (z : ℍ) : ℂ :=
  lpsChi4PrimeE2Twist q (lpsE2AffineMatrix m hm 0 • z)
lemma lpsChi4PrimeE2Dilate_eq (q m : ℕ) [Fact q.Prime] (hm : 0 < m) :
    lpsChi4PrimeE2Dilate q m hm=(fun z : ℍ =>
      (gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))⁻¹ *
        ∑ r : Fin 4,lpsChi4E2Character (r.val:ZMod 4)*
          ((gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹ *
            ∑ a : Fin q,lpsQuadraticE2Character q (a.val:ZMod q)*EisensteinSeries.E2
              (lpsE2AffineMatrix m hm (((q*r.val+4*a.val:ℕ):ℝ)/((4*q:ℕ):ℝ)) • z))) := by
  funext z
  unfold lpsChi4PrimeE2Dilate lpsChi4PrimeE2Twist lpsQuadraticE2Twist
  apply congrArg (fun w : ℂ => (gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))⁻¹*w)
  apply Finset.sum_congr rfl
  intro r hr
  apply congrArg (fun w : ℂ => lpsChi4E2Character (r.val:ZMod 4)*w)
  apply congrArg (fun w : ℂ => (gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹*w)
  apply Finset.sum_congr rfl
  intro a ha
  apply congrArg (fun w : ℂ => lpsQuadraticE2Character q (a.val:ZMod q)*w)
  apply congrArg EisensteinSeries.E2
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_vadd,UpperHalfPlane.coe_vadd,lpsE2AffineMatrix_action,lpsE2AffineMatrix_action]
  simp only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_zero,add_zero]
  have hqC : (q:ℂ)≠0 := by exact_mod_cast NeZero.ne q
  push_cast
  field_simp [hqC]
  ring
lemma lpsFiniteWeighted_SL_slash (α : Type*) [Fintype α] (G : ℂ) (c : α→ℂ)
    (f : α→ℍ→ℂ) (γ : SL(2,ℤ)) :
    ((fun z => G*∑ i : α,c i*f i z) ∣[(2:ℤ)] γ)=
      (fun z => G*∑ i : α,c i*((f i ∣[(2:ℤ)] γ) z)) := by
  classical
  funext z
  simp only [ModularForm.SL_slash_apply]
  rw [mul_assoc,Finset.sum_mul]
  apply congrArg (fun w : ℂ => G*w)
  apply Finset.sum_congr rfl
  intro i hi
  ring
lemma lpsChi4PrimeE2Dilate_cusp_tendsto (q m : ℕ) [Fact q.Prime] (hm : 0 < m) (γ : SL(2,ℤ)) :
    Tendsto (lpsChi4PrimeE2Dilate q m hm ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 ((gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))⁻¹ *
        ∑ r : Fin 4,lpsChi4E2Character (r.val:ZMod 4)*
          ((gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹ *
            ∑ a : Fin q,lpsQuadraticE2Character q (a.val:ZMod q)*
              (((Int.gcd (((4*q:ℕ):ℤ)*(m:ℤ)*γ 0 0+((q*r.val+4*a.val:ℕ):ℤ)*γ 1 0)
                (((4*q:ℕ):ℤ)*γ 1 0):ℕ):ℂ)^2/(((4*q:ℕ):ℂ)^2*(m:ℂ)^2))))) := by
  classical
  have hp : 0 < 4*q := Nat.mul_pos (by decide) (Fact.out : q.Prime).pos
  have hs := tendsto_finsetSum Finset.univ (fun (r : Fin 4) hr =>
    ((tendsto_finsetSum Finset.univ (fun (a : Fin q) ha =>
      (lpsE2Affine_cusp_tendsto m (4*q) hm hp ((q*r.val+4*a.val:ℕ):ℤ) γ).const_mul
        (lpsQuadraticE2Character q (a.val:ZMod q)))).const_mul
      (gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹).const_mul
        (lpsChi4E2Character (r.val:ZMod 4)))
  have h := hs.const_mul (gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))⁻¹
  rw [lpsChi4PrimeE2Dilate_eq,lpsFiniteWeighted_SL_slash]
  simp_rw [lpsFiniteWeighted_SL_slash]
  simpa only [Int.cast_natCast] using h
lemma lpsChi4PrimeE2Dilate_one (q : ℕ) [Fact q.Prime] :
    lpsChi4PrimeE2Dilate q 1 (by decide)=lpsChi4PrimeE2Twist q := by
  funext z
  unfold lpsChi4PrimeE2Dilate
  apply congrArg (lpsChi4PrimeE2Twist q)
  apply UpperHalfPlane.ext
  rw [lpsE2AffineMatrix_action]
  simp
lemma lpsChi4PrimeE2Twist_bounded_at_cusps (q : ℕ) [Fact q.Prime]
    (c : OnePoint ℝ) (hc : IsCusp c 𝒮ℒ) : OnePoint.IsBoundedAt c (lpsChi4PrimeE2Twist q) 2 := by
  apply (OnePoint.isBoundedAt_iff_forall_SL2Z hc).mpr
  intro γ hγ
  have ht := lpsChi4PrimeE2Dilate_cusp_tendsto q 1 (by decide) γ
  rw [lpsChi4PrimeE2Dilate_one] at ht
  exact ht.isBigO_one ℝ
noncomputable def lpsChi4PrimeE2TwistModularForm (q : ℕ) [Fact q.Prime] (hq2 : q≠2) :
    ModularForm (CongruenceSubgroup.Gamma0 ((4*q)^2) : Subgroup (GL (Fin 2) ℝ)) 2 where
  toFun := lpsChi4PrimeE2Twist q
  slash_action_eq' := by
    intro g hg
    obtain ⟨γ,hγ,rfl⟩ := hg
    simpa [Matrix.SpecialLinearGroup.mapGL,←ModularForm.SL_slash] using lpsChi4PrimeE2Twist_slash_gamma0 q hq2 γ hγ
  holo' := lpsChi4PrimeE2Twist_mdifferentiable q
  bdd_at_cusps' := fun hc => lpsChi4PrimeE2Twist_bounded_at_cusps q _
    (hc.mono (Subgroup.map_le_range (Matrix.SpecialLinearGroup.mapGL ℝ) _))
end QEC.Coding.TannerLiftedProduct


