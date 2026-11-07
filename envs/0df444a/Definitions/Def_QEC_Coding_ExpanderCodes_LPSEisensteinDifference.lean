-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
-- name    : QEC_Coding_ExpanderCodes_LPSEisensteinDifference
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:11:28.974864+00:00
-- url     : https://prove2.me/theorems/ca4bc6df-c3dd-41b7-addd-af2b42733dea
-- title:
--   LPSEisenstein Difference
-- statement:
--   Definitions and structural lemmas for LPSEisenstein Difference, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEisensteinDifference.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2AffineMatrix_action
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2AffineMatrix_det
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2Affine_cusp_tendsto
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2_slash_tendsto_one
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
noncomputable def lpsE2Difference (m : ℕ) (hm : 0 < m) (z : ℍ) : ℂ :=
  EisensteinSeries.E2 z-(m:ℂ)*EisensteinSeries.E2 (lpsE2AffineMatrix m hm 0 • z)
lemma lpsE2Difference_cusp_tendsto (m : ℕ) (hm : 0 < m) (γ : SL(2,ℤ)) :
    Tendsto (lpsE2Difference m hm ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 (1-((Int.gcd ((m:ℤ)*γ 0 0) (γ 1 0):ℕ):ℂ)^2/(m:ℂ))) := by
  have hE := lpsE2_slash_tendsto_one γ
  have hM := lpsE2Affine_cusp_tendsto m 1 hm (by decide) 0 γ
  simp only [Nat.cast_one,zero_mul,one_mul,add_zero,
    one_pow] at hM
  have h := hE.sub (hM.const_mul (m:ℂ))
  have hmC : (m:ℂ)≠0 := by exact_mod_cast hm.ne'
  have hv : 1-(m:ℂ)*(((Int.gcd ((m:ℤ)*γ 0 0) (γ 1 0):ℕ):ℂ)^2/(m:ℂ)^2) =
      1-((Int.gcd ((m:ℤ)*γ 0 0) (γ 1 0):ℕ):ℂ)^2/(m:ℂ) := by
    field_simp [hmC]
  rw [hv] at h
  convert h using 1
  funext z
  simp only [ModularForm.SL_slash_apply,lpsE2Difference]
  ring
lemma lpsE2DilationConjugate_det (m : ℕ) (γ : SL(2,ℤ)) (k : ℤ)
    (hc : γ 1 0=(m:ℤ)*k) :
    Matrix.det !![γ 0 0,(m:ℤ)*γ 0 1;k,γ 1 1]=1 := by
  have hd : γ 0 0*γ 1 1-γ 0 1*γ 1 0=1 := by
    simpa only [Matrix.det_fin_two] using γ.det_coe
  rw [hc] at hd
  rw [Matrix.det_fin_two]
  change γ 0 0*γ 1 1-((m:ℤ)*γ 0 1)*k=1
  linear_combination hd
def lpsE2DilationConjugate (m : ℕ) (γ : SL(2,ℤ)) (k : ℤ)
    (hc : γ 1 0=(m:ℤ)*k) : SL(2,ℤ) :=
  ⟨!![γ 0 0,(m:ℤ)*γ 0 1;k,γ 1 1],lpsE2DilationConjugate_det m γ k hc⟩
lemma lpsE2DilationConjugate_action (m : ℕ) (hm : 0 < m) (γ δ : SL(2,ℤ))
    (k : ℤ) (hc : γ 1 0=(m:ℤ)*k)
    (h00 : δ 0 0=γ 0 0) (h01 : δ 0 1=(m:ℤ)*γ 0 1)
    (h10 : δ 1 0=k) (h11 : δ 1 1=γ 1 1) (z : ℍ) :
    δ • (lpsE2AffineMatrix m hm 0 • z) = lpsE2AffineMatrix m hm 0 • (γ • z) := by
  have hd : (γ 1 0:ℂ)*(z:ℂ)+(γ 1 1:ℂ)≠0 := by
    simpa only [ModularGroup.denom_apply] using UpperHalfPlane.denom_ne_zero γ z
  rw [hc] at hd
  push_cast at hd
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply,lpsE2AffineMatrix_action,
    lpsE2AffineMatrix_action,UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [Complex.ofReal_zero,add_zero,algebraMap_int_eq,Int.coe_castRingHom,
    Complex.ofReal_intCast]
  rw [h00,h01,h10,h11,hc]
  push_cast
  field_simp [hd]
lemma lpsE2DilationConjugate_denom (m : ℕ) (hm : 0 < m) (γ δ : SL(2,ℤ))
    (k : ℤ) (hc : γ 1 0=(m:ℤ)*k) (h10 : δ 1 0=k) (h11 : δ 1 1=γ 1 1) (z : ℍ) :
    UpperHalfPlane.denom δ ((lpsE2AffineMatrix m hm 0 • z:ℍ):ℂ)=
      UpperHalfPlane.denom γ (z:ℂ) := by
  rw [ModularGroup.denom_apply,ModularGroup.denom_apply,lpsE2AffineMatrix_action,
    h10,h11,hc]
  push_cast
  ring
lemma lpsE2DilationConjugate_D2 (m : ℕ) (hm : 0 < m) (γ δ : SL(2,ℤ))
    (k : ℤ) (hc : γ 1 0=(m:ℤ)*k) (h10 : δ 1 0=k) (h11 : δ 1 1=γ 1 1) (z : ℍ) :
    EisensteinSeries.D2 δ (lpsE2AffineMatrix m hm 0 • z)=
      (m:ℂ)⁻¹*EisensteinSeries.D2 γ z := by
  have hd : UpperHalfPlane.denom γ (z:ℂ)≠0 := UpperHalfPlane.denom_ne_zero γ z
  have hmC : (m:ℂ)≠0 := by exact_mod_cast hm.ne'
  simp only [EisensteinSeries.D2]
  rw [lpsE2DilationConjugate_denom m hm γ δ k hc h10 h11 z,h10,hc]
  push_cast
  field_simp [hmC,hd]
lemma lpsE2Dilated_slash_of_entries (m : ℕ) (hm : 0 < m) (γ δ : SL(2,ℤ))
    (k : ℤ) (hc : γ 1 0=(m:ℤ)*k)
    (h00 : δ 0 0=γ 0 0) (h01 : δ 0 1=(m:ℤ)*γ 0 1)
    (h10 : δ 1 0=k) (h11 : δ 1 1=γ 1 1) (z : ℍ) :
    (((fun w : ℍ => EisensteinSeries.E2 (lpsE2AffineMatrix m hm 0 • w))
      ∣[(2:ℤ)] γ) z)=
      EisensteinSeries.E2 (lpsE2AffineMatrix m hm 0 • z)-
        (1/(2*riemannZeta 2))*(m:ℂ)⁻¹*EisensteinSeries.D2 γ z := by
  have h := congrFun (EisensteinSeries.E2_slash_action δ) (lpsE2AffineMatrix m hm 0 • z)
  simp only [ModularForm.SL_slash_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at h ⊢
  rw [lpsE2DilationConjugate_action m hm γ δ k hc h00 h01 h10 h11 z,
    lpsE2DilationConjugate_denom m hm γ δ k hc h10 h11 z,
    lpsE2DilationConjugate_D2 m hm γ δ k hc h10 h11 z] at h
  simpa only [mul_assoc] using h
lemma lpsE2Dilated_slash (m : ℕ) (hm : 0 < m) (γ : SL(2,ℤ)) (k : ℤ)
    (hc : γ 1 0=(m:ℤ)*k) (z : ℍ) :
    (((fun w : ℍ => EisensteinSeries.E2 (lpsE2AffineMatrix m hm 0 • w))
      ∣[(2:ℤ)] γ) z)=
      EisensteinSeries.E2 (lpsE2AffineMatrix m hm 0 • z)-
        (1/(2*riemannZeta 2))*(m:ℂ)⁻¹*EisensteinSeries.D2 γ z :=
  lpsE2Dilated_slash_of_entries m hm γ (lpsE2DilationConjugate m γ k hc) k hc rfl rfl rfl rfl z
lemma lpsE2Difference_slash_gamma0 (m : ℕ) (hm : 0 < m) (γ : SL(2,ℤ))
    (hγ : γ∈CongruenceSubgroup.Gamma0 m) :
    (lpsE2Difference m hm ∣[(2:ℤ)] γ)=lpsE2Difference m hm := by
  rw [CongruenceSubgroup.Gamma0_mem] at hγ
  have hdvd : (m:ℤ)∣γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (γ 1 0) m).mp hγ
  obtain ⟨k,hk⟩ := hdvd
  have hmC : (m:ℂ)≠0 := by exact_mod_cast hm.ne'
  have hE := congrFun (EisensteinSeries.E2_slash_action γ)
  funext z
  have hM := lpsE2Dilated_slash m hm γ k hk z
  have hEz := hE z
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at hEz
  have he : ((lpsE2Difference m hm ∣[(2:ℤ)] γ) z)=
      ((EisensteinSeries.E2 ∣[(2:ℤ)] γ) z)-(m:ℂ)*
        (((fun w : ℍ => EisensteinSeries.E2 (lpsE2AffineMatrix m hm 0 • w))
          ∣[(2:ℤ)] γ) z) := by
    simp only [ModularForm.SL_slash_apply,lpsE2Difference]
    ring
  rw [he,hEz,hM,lpsE2Difference]
  have he : (m:ℂ)*((1/(2*riemannZeta 2))*(m:ℂ)⁻¹*EisensteinSeries.D2 γ z)=
      (1/(2*riemannZeta 2))*EisensteinSeries.D2 γ z := by
    calc _=((m:ℂ)*(m:ℂ)⁻¹)*((1/(2*riemannZeta 2))*EisensteinSeries.D2 γ z) := by ring
         _=_ := by rw [mul_inv_cancel₀ hmC];simp
  rw [mul_sub,he]
  ring
lemma lpsE2Difference_mdifferentiable (m : ℕ) (hm : 0 < m) : MDiff (lpsE2Difference m hm) := by
  have hp : 0<(lpsE2AffineMatrix m hm 0).det.val := by
    rw [lpsE2AffineMatrix_det]
    exact_mod_cast hm
  have h := E2_mdifferentiable.sub
    ((E2_mdifferentiable.comp (UpperHalfPlane.mdifferentiable_smul hp)).const_smul (m:ℂ))
  exact h
lemma lpsE2Difference_bounded_at_cusps (m : ℕ) (hm : 0 < m)
    (c : OnePoint ℝ) (hc : IsCusp c 𝒮ℒ) : OnePoint.IsBoundedAt c (lpsE2Difference m hm) 2 := by
  apply (OnePoint.isBoundedAt_iff_forall_SL2Z hc).mpr
  intro γ hγ
  exact (lpsE2Difference_cusp_tendsto m hm γ).isBigO_one ℝ
noncomputable def lpsE2DifferenceModularForm (m : ℕ) (hm : 0 < m) :
    ModularForm (CongruenceSubgroup.Gamma0 m : Subgroup (GL (Fin 2) ℝ)) 2 where
  toFun := lpsE2Difference m hm
  slash_action_eq' := by
    intro g hg
    obtain ⟨γ,hγ,rfl⟩ := hg
    simpa [Matrix.SpecialLinearGroup.mapGL,← ModularForm.SL_slash] using
      lpsE2Difference_slash_gamma0 m hm γ hγ
  holo' := lpsE2Difference_mdifferentiable m hm
  bdd_at_cusps' := fun hc => lpsE2Difference_bounded_at_cusps m hm _
    (hc.mono (Subgroup.map_le_range (Matrix.SpecialLinearGroup.mapGL ℝ) _))
noncomputable def lpsE2DilationCoefficient (m n : ℕ) : ℂ :=
  if m∣n then (if n/m=0 then 1 else -24*(ArithmeticFunction.sigma 1 (n/m):ℂ)) else 0
noncomputable def lpsE2DifferenceCoefficient (m n : ℕ) : ℂ :=
  (if n=0 then 1 else -24*(ArithmeticFunction.sigma 1 n:ℂ))-(m:ℂ)*lpsE2DilationCoefficient m n
end QEC.Coding.TannerLiftedProduct


