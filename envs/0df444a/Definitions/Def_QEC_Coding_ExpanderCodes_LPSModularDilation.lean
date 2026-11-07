-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
-- name    : QEC_Coding_ExpanderCodes_LPSModularDilation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:13:13.676689+00:00
-- url     : https://prove2.me/theorems/dc317ef1-31fd-43d1-8eb2-79debb64ef82
-- title:
--   LPSModular Dilation
-- statement:
--   Definitions and structural lemmas for LPSModular Dilation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularDilation.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIteratedEisenstein
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2AffineMatrix_coe
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2AffineMatrix_det
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
lemma lpsGamma0_level_le (N L : ℕ) (hNL : N ∣ L) :
    CongruenceSubgroup.Gamma0 L ≤ CongruenceSubgroup.Gamma0 N := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma0_mem] at hγ ⊢
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd (γ 1 0) N).mpr
  have hL := (ZMod.intCast_zmod_eq_zero_iff_dvd (γ 1 0) L).mp hγ
  exact (by exact_mod_cast hNL : (N:ℤ) ∣ (L:ℤ)).trans hL
noncomputable def lpsModularForm_raiseLevel (N L : ℕ) (hNL : N ∣ L)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    ModularForm (CongruenceSubgroup.Gamma0 L : Subgroup (GL (Fin 2) ℝ)) 2 where
  toFun := f
  slash_action_eq' := fun g hg => f.slash_action_eq' g
    ((Subgroup.map_mono (lpsGamma0_level_le N L hNL)) hg)
  holo' := f.holo'
  bdd_at_cusps' := fun hc => f.bdd_at_cusps'
    (hc.mono (Subgroup.map_mono (lpsGamma0_level_le N L hNL)))
lemma lpsFunction_affine_slash (f : ℍ→ℂ) (m : ℕ) (hm : 0 < m) (r : ℝ) :
    (f ∣[(2:ℤ)] lpsE2AffineMatrix m hm r)=
      (fun z : ℍ => (m:ℂ)*f (lpsE2AffineMatrix m hm r • z)) := by
  ext z
  simp [ModularForm.slash_apply,UpperHalfPlane.σ,hm,UpperHalfPlane.denom,
    lpsE2AffineMatrix_coe,Matrix.of_apply,mul_comm]
lemma lpsFunction_dilate_SL_slash_of_entries (f : ℍ→ℂ) (m : ℕ) (hm : 0 < m)
    (γ δ : SL(2,ℤ)) (k : ℤ) (hc : γ 1 0=(m:ℤ)*k)
    (h00 : δ 0 0=γ 0 0) (h01 : δ 0 1=(m:ℤ)*γ 0 1)
    (h10 : δ 1 0=k) (h11 : δ 1 1=γ 1 1) (z : ℍ) :
    (((fun w : ℍ => f (lpsE2AffineMatrix m hm 0 • w)) ∣[(2:ℤ)] γ) z)=
      ((f ∣[(2:ℤ)] δ) (lpsE2AffineMatrix m hm 0 • z)) := by
  simp only [ModularForm.SL_slash_apply]
  rw [lpsE2DilationConjugate_action m hm γ δ k hc h00 h01 h10 h11,
    lpsE2DilationConjugate_denom m hm γ δ k hc h10 h11]
lemma lpsModularForm_dilate_slash_gamma0 (N m : ℕ) (hm : 0 < m)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 (N*m)) :
    ((fun z : ℍ => f (lpsE2AffineMatrix m hm 0 • z)) ∣[(2:ℤ)] γ)=
      (fun z : ℍ => f (lpsE2AffineMatrix m hm 0 • z)) := by
  rw [CongruenceSubgroup.Gamma0_mem] at hγ
  obtain ⟨t,ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (γ 1 0) (N*m)).mp hγ
  have hc : γ 1 0=(m:ℤ)*((N:ℤ)*t) := by
    rw [ht];push_cast;ring
  let δ := lpsE2DilationConjugate m γ ((N:ℤ)*t) hc
  have hδ : δ∈CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]
    change (((N:ℤ)*t:ℤ):ZMod N)=0
    simp
  have hg : Matrix.SpecialLinearGroup.mapGL ℝ δ ∈
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) := ⟨δ,hδ,rfl⟩
  have hf : ((f:ℍ→ℂ) ∣[(2:ℤ)] δ)=(f:ℍ→ℂ) := by
    simpa [Matrix.SpecialLinearGroup.mapGL,←ModularForm.SL_slash,ModularForm.toSlashInvariantForm_coe] using
      SlashInvariantFormClass.slash_action_eq (Γ := (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) (k := (2:ℤ)) f (Matrix.SpecialLinearGroup.mapGL ℝ δ) hg
  funext z
  rw [lpsFunction_dilate_SL_slash_of_entries _ m hm γ δ ((N:ℤ)*t) hc rfl rfl rfl rfl,hf]
noncomputable def lpsDilationRationalMatrix (m : ℕ) (hm : 0 < m) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(m:ℚ),0;0,1] (by
    rw [Matrix.det_fin_two];simpa using (show (m:ℚ)≠0 by exact_mod_cast hm.ne'))
lemma lpsDilationRationalMatrix_map (m : ℕ) (hm : 0 < m) :
    (lpsDilationRationalMatrix m hm).map (Rat.castHom ℝ)=lpsE2AffineMatrix m hm 0 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lpsDilationRationalMatrix,lpsE2AffineMatrix,Matrix.of_apply]
lemma lpsModularForm_dilate_bounded_at_cusps (N m : ℕ) [NeZero N] (hm : 0 < m)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (c : OnePoint ℝ) (hc : IsCusp c 𝒮ℒ) :
    OnePoint.IsBoundedAt c (fun z : ℍ => f (lpsE2AffineMatrix m hm 0 • z)) 2 := by
  have hs := lpsRationalGL_smul_cusp (lpsDilationRationalMatrix m hm) c hc
  rw [lpsDilationRationalMatrix_map] at hs
  have hsg : IsCusp (lpsE2AffineMatrix m hm 0 • c)
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) :=
    (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mpr hs
  have hb : OnePoint.IsBoundedAt c ((f:ℍ→ℂ) ∣[(2:ℤ)] lpsE2AffineMatrix m hm 0) 2 :=
    OnePoint.IsBoundedAt.smul_iff.mp (f.bdd_at_cusps' hsg)
  rw [lpsFunction_affine_slash] at hb
  have h := lpsCuspBounded_const_smul c _ (m:ℂ)⁻¹ hb
  have hmC : (m:ℂ)≠0 := by exact_mod_cast hm.ne'
  have he : ((m:ℂ)⁻¹ • (fun z : ℍ => (m:ℂ)*f (lpsE2AffineMatrix m hm 0 • z)))=
      (fun z : ℍ => f (lpsE2AffineMatrix m hm 0 • z)) := by
    funext z
    simp [Pi.smul_apply,smul_eq_mul,hmC]
  rw [he] at h
  exact h
noncomputable def lpsModularForm_dilate (N m : ℕ) [NeZero N] (hm : 0 < m)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    ModularForm (CongruenceSubgroup.Gamma0 (N*m) : Subgroup (GL (Fin 2) ℝ)) 2 where
  toFun := fun z => f (lpsE2AffineMatrix m hm 0 • z)
  slash_action_eq' := by
    intro g hg
    obtain ⟨γ,hγ,rfl⟩ := hg
    simpa [Matrix.SpecialLinearGroup.mapGL,←ModularForm.SL_slash] using
      lpsModularForm_dilate_slash_gamma0 N m hm f γ hγ
  holo' := by
    apply f.holo'.comp
    apply UpperHalfPlane.mdifferentiable_smul
    rw [lpsE2AffineMatrix_det]
    exact_mod_cast hm
  bdd_at_cusps' := fun hc => lpsModularForm_dilate_bounded_at_cusps N m hm f _
    (hc.mono (Subgroup.map_le_range (Matrix.SpecialLinearGroup.mapGL ℝ) _))
noncomputable def lpsModularDilationCoefficient (a : ℕ→ℂ) (m n : ℕ) : ℂ :=
  if m∣n then a (n/m) else 0
noncomputable def lpsChi4E2DilateModularForm (m : ℕ) (hm : 0 < m) :
    ModularForm (CongruenceSubgroup.Gamma0 (16*m) : Subgroup (GL (Fin 2) ℝ)) 2 :=
  lpsModularForm_dilate 16 m hm lpsChi4E2TwistModularForm
noncomputable def lpsQuadraticE2DilateModularForm (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (m : ℕ) (hm : 0 < m) :
    ModularForm (CongruenceSubgroup.Gamma0 (q^2*m) : Subgroup (GL (Fin 2) ℝ)) 2 :=
  lpsModularForm_dilate (q^2) m hm (lpsQuadraticE2TwistModularForm q hq2)
noncomputable def lpsChi4PrimeE2DilateModularForm (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (m : ℕ) (hm : 0 < m) :
    ModularForm (CongruenceSubgroup.Gamma0 ((4*q)^2*m) : Subgroup (GL (Fin 2) ℝ)) 2 :=
  lpsModularForm_dilate ((4*q)^2) m hm (lpsChi4PrimeE2TwistModularForm q hq2)
lemma lpsThetaBasis_level_dvd (q : ℕ) (a : Fin 5) (b : Fin 3) :
    2^a.val*q^b.val ∣ (4*q)^2 := by
  have h2 : 2^a.val ∣ (2:ℕ)^4 := pow_dvd_pow 2 (by omega)
  have hq : q^b.val ∣ q^2 := pow_dvd_pow q (by omega)
  have h := mul_dvd_mul h2 hq
  norm_num only [Nat.reducePow] at h
  simpa only [mul_pow,Nat.reducePow] using h
noncomputable def lpsE2DifferenceThetaBasis (q : ℕ) [Fact q.Prime] (a : Fin 5) (b : Fin 3) :
    ModularForm (CongruenceSubgroup.Gamma0 ((4*q)^2) : Subgroup (GL (Fin 2) ℝ)) 2 :=
  lpsModularForm_raiseLevel (2^a.val*q^b.val) ((4*q)^2)
    (lpsThetaBasis_level_dvd q a b)
    (lpsE2DifferenceModularForm (2^a.val*q^b.val)
      (mul_pos (pow_pos (by decide) _) (pow_pos (Fact.out : q.Prime).pos _)))
noncomputable def lpsChi4E2ThetaBasis (q : ℕ) [Fact q.Prime] (b : Fin 3) :
    ModularForm (CongruenceSubgroup.Gamma0 ((4*q)^2) : Subgroup (GL (Fin 2) ℝ)) 2 :=
  lpsModularForm_raiseLevel (16*q^b.val) ((4*q)^2)
    (by simpa using lpsThetaBasis_level_dvd q (4:Fin 5) b)
    (lpsChi4E2DilateModularForm (q^b.val) (pow_pos (Fact.out : q.Prime).pos _))
noncomputable def lpsQuadraticE2ThetaBasis (q : ℕ) [Fact q.Prime] (hq2 : q≠2) (a : Fin 5) :
    ModularForm (CongruenceSubgroup.Gamma0 ((4*q)^2) : Subgroup (GL (Fin 2) ℝ)) 2 :=
  lpsModularForm_raiseLevel (q^2*2^a.val) ((4*q)^2)
    (by
      have h := lpsThetaBasis_level_dvd q a (2:Fin 3)
      change 2^a.val*q^2 ∣ (4*q)^2 at h
      simpa only [mul_comm] using h)
    (lpsQuadraticE2DilateModularForm q hq2 (2^a.val) (pow_pos (by decide) _))
end QEC.Coding.TannerLiftedProduct


