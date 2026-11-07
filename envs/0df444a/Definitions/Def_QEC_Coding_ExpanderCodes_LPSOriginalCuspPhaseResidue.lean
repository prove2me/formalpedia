-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspPhaseResidue
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalCuspPhaseResidue
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T00:08:08.502518+00:00
-- url     : https://prove2.me/theorems/a74106fb-e3a4-451d-b6aa-be152cae622a
-- title:
--   LPSOriginal Cusp Phase Residue
-- statement:
--   Definitions and structural lemmas for LPSOriginal Cusp Phase Residue, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspPhaseResidue.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.KummerExtension
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2AffineMatrix_action
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2AffineMatrix_coe
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2AffineMatrix_det
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2SLInverse_real_matrix
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDilationColumnGcdDvd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


set_option autoImplicit false
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
namespace QEC.Coding.TannerLiftedProduct
noncomputable section
lemma lpsOriginalDilatedAtScaledCuspIntegralShift (N : ℕ) (hN : 0<N) (γ : SL(2,ℤ)) :
    ∃ r : ℚ, (∃ z : ℤ, (N : ℚ) * r = z) ∧ ∀ σ : ℍ,
      lpsOriginalJDilated N hN (γ • (lpsE2AffineMatrix N hN 0 • σ))=
        lpsOriginalJInvariant
          (lpsE2AffineMatrix ((Int.gcd ((N:ℤ)*γ 0 0) (γ 1 0))^2)
            (pow_pos (lpsOriginalDilationColumnGcdPos N hN γ) 2) (r:ℝ) • σ) := by
  let g : ℕ := Int.gcd ((N:ℤ)*γ 0 0) (γ 1 0)
  have hg : 0<g := lpsOriginalDilationColumnGcdPos N hN γ
  obtain ⟨a,c,hcop,ha,hc⟩ := Int.exists_gcd_one hg
  let δ := lpsE2IntegerPrimitiveColumn a c hcop
  let M : GL (Fin 2) ℝ := lpsE2AffineMatrix N hN 0*Matrix.SpecialLinearGroup.mapGL ℝ γ
  have hdetM : M.det.val=(N:ℝ) := by
    calc M.det.val=(lpsE2AffineMatrix N hN 0).det.val := by simp [M]
         _=(N:ℝ) := lpsE2AffineMatrix_det N hN 0
  have hM00 : M 0 0=((N:ℤ)*γ 0 0:ℤ) := by
    simp [M,lpsE2AffineMatrix_coe,Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.mul_apply,Fin.sum_univ_two,Matrix.map,Matrix.of_apply]
  have hM10 : M 1 0=(γ 1 0:ℝ) := by
    simp [M,lpsE2AffineMatrix_coe,Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.mul_apply,Fin.sum_univ_two,Matrix.map,Matrix.of_apply]
  have hA : (δ 0 0:ℝ)*(g:ℝ)=M 0 0 := by
    rw [hM00]
    change (a:ℝ)*(g:ℝ)=(((N:ℤ)*γ 0 0:ℤ):ℝ)
    exact_mod_cast ha.symm
  have hC : (δ 1 0:ℝ)*(g:ℝ)=M 1 0 := by
    rw [hM10]
    change (c:ℝ)*(g:ℝ)=(γ 1 0:ℝ)
    exact_mod_cast hc.symm
  let h : GL (Fin 2) ℝ := (Matrix.SpecialLinearGroup.mapGL ℝ δ)⁻¹*M
  have hdδ : (δ 0 0:ℝ)*(δ 1 1:ℝ)-(δ 0 1:ℝ)*(δ 1 0:ℝ)=1 := by
    have he : δ 0 0*δ 1 1-δ 0 1*δ 1 0=1 := by
      simpa only [Matrix.det_fin_two] using δ.det_coe
    exact_mod_cast he
  have hh10 : h 1 0=0 := by
    change ((((Matrix.SpecialLinearGroup.mapGL ℝ δ)⁻¹:GL (Fin 2) ℝ):Matrix (Fin 2) (Fin 2) ℝ)*
      (M:Matrix (Fin 2) (Fin 2) ℝ)) 1 0=0
    rw [lpsE2SLInverse_real_matrix]
    simp [Matrix.mul_apply,Fin.sum_univ_two,Matrix.of_apply]
    rw [←hA,←hC]
    ring
  have hh00 : h 0 0=(g:ℝ) := by
    change ((((Matrix.SpecialLinearGroup.mapGL ℝ δ)⁻¹:GL (Fin 2) ℝ):Matrix (Fin 2) (Fin 2) ℝ)*
      (M:Matrix (Fin 2) (Fin 2) ℝ)) 0 0=(g:ℝ)
    rw [lpsE2SLInverse_real_matrix]
    simp [Matrix.mul_apply,Fin.sum_univ_two,Matrix.of_apply]
    rw [←hA,←hC]
    linear_combination (g:ℝ)*hdδ
  have hhdet : h.det.val=(N:ℝ) := by simp [h,hdetM]
  have hgR : (g:ℝ)≠0 := by exact_mod_cast hg.ne'
  have hh11 : h 1 1=(N:ℝ)/(g:ℝ) := by
    apply (eq_div_iff hgR).2
    have he := hhdet
    change Matrix.det (h:Matrix (Fin 2) (Fin 2) ℝ)=(N:ℝ) at he
    simpa only [Matrix.det_fin_two,hh00,hh10,mul_zero,zero_mul,sub_zero,mul_comm] using he
  let b : ℤ := δ 1 1*((N:ℤ)*γ 0 1)-δ 0 1*γ 1 1
  have hh01 : h 0 1=(b:ℝ) := by
    change ((((Matrix.SpecialLinearGroup.mapGL ℝ δ)⁻¹:GL (Fin 2) ℝ):Matrix (Fin 2) (Fin 2) ℝ)*
      (M:Matrix (Fin 2) (Fin 2) ℝ)) 0 1=(b:ℝ)
    rw [lpsE2SLInverse_real_matrix]
    simp [M,b,lpsE2AffineMatrix_coe,Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.mul_apply,Fin.sum_univ_two,Matrix.map,Matrix.of_apply,
      Matrix.vecHead,Matrix.vecTail,sub_eq_add_neg]
  let r : ℚ := (b:ℚ)*(g:ℚ)/(N:ℚ)
  have hr : (r:ℝ)=h 0 1*(g:ℝ)/(N:ℝ) := by
    rw [hh01]
    simp only [r,Rat.cast_div,Rat.cast_mul,Rat.cast_intCast,Rat.cast_natCast]
  refine ⟨r, ⟨?_, ?_⟩⟩
  · refine ⟨b * (g : ℤ), ?_⟩
    have hNQ : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
    dsimp [r]
    push_cast
    field_simp [hNQ]
  intro σ
  have hp : 0<h.det.val := by rw [hhdet];exact_mod_cast hN
  have he : h • (lpsE2AffineMatrix N hN 0 • σ)=
      lpsE2AffineMatrix (g^2) (pow_pos hg 2) (r:ℝ) • σ := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_smul_of_det_pos hp,lpsE2AffineMatrix_action,
      UpperHalfPlane.num,UpperHalfPlane.denom,hh00,hh10,hh11,lpsE2AffineMatrix_action]
    simp only [Complex.ofReal_div,Complex.ofReal_zero,Complex.ofReal_natCast,zero_mul,
      zero_add,add_zero,Nat.cast_pow]
    have hgC : (g:ℂ)≠0 := by exact_mod_cast hg.ne'
    have hNC : (N:ℂ)≠0 := by exact_mod_cast hN.ne'
    rw [hr]
    change ((g:ℂ)*((N:ℂ)*(σ:ℂ))+(h 0 1:ℂ))/((N:ℂ)/(g:ℂ))=
      (g:ℂ)^2*(σ:ℂ)+(h 0 1*(g:ℝ)/(N:ℝ):ℝ)
    push_cast
    field_simp [hgC,hNC]
  have hm : M=Matrix.SpecialLinearGroup.mapGL ℝ δ*h := by simp [h]
  have hγ : ∀ τ : ℍ, γ•τ=Matrix.SpecialLinearGroup.mapGL ℝ γ•τ := by
    intro τ
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_specialLinearGroup_apply,
      UpperHalfPlane.coe_smul_of_det_pos (by simp)]
    simp [UpperHalfPlane.num,UpperHalfPlane.denom,Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.map,Matrix.of_apply]
  calc
    lpsOriginalJDilated N hN (γ • (lpsE2AffineMatrix N hN 0 • σ))=
        lpsOriginalJInvariant (M • (lpsE2AffineMatrix N hN 0 • σ)) := by
      simp only [lpsOriginalJDilated,M,mul_smul,hγ]
    _=lpsOriginalJInvariant (Matrix.SpecialLinearGroup.mapGL ℝ δ •
        (h • (lpsE2AffineMatrix N hN 0 • σ))) := by rw [hm,mul_smul]
    _=lpsOriginalJInvariant (h • (lpsE2AffineMatrix N hN 0 • σ)) :=
      lpsOriginalJInvariant_SL_invariant _ ⟨δ,rfl⟩ _
    _=_ := by rw [he]
lemma lpsOriginalLevelNomePhase_pow (N : ℕ) (r : ℚ)
    (hr : ∃ z : ℤ, (N : ℚ) * r = z) :
    (Function.Periodic.qParam 1 (r : ℂ))^N = 1 := by
  obtain ⟨z,hz⟩ := hr
  have hzC : (N : ℂ) * (r : ℂ) = (z : ℂ) := by exact_mod_cast hz
  simp only [Function.Periodic.qParam,Complex.ofReal_one,div_one]
  rw [← Complex.exp_nat_mul]
  apply Complex.exp_eq_one_iff.mpr
  refine ⟨z, ?_⟩
  calc
    (N : ℂ) * (2 * Real.pi * I * (r : ℂ)) =
        (2 * Real.pi * I) * ((N : ℂ) * (r : ℂ)) := by ring
    _ = (z : ℂ) * (2 * Real.pi * I) := by rw [hzC];ring
lemma lpsOriginalSLAtScaledCuspIntegralShift (N : ℕ) (hN : 0<N) (g : 𝒮ℒ) :
    ∃ m : ℕ, ∃ hm : 0<m, ∃ r : ℚ, m≤N^2 ∧ (∃ z : ℤ, (N : ℚ) * r = z) ∧ ∀ σ : ℍ,
      lpsOriginalJDilated N hN (g.val • (lpsE2AffineMatrix N hN 0 • σ))=
        lpsOriginalJInvariant (lpsE2AffineMatrix m hm (r:ℝ) • σ) := by
  obtain ⟨γ,hγ⟩ := g.property
  have ha : ∀ τ : ℍ,γ•τ=Matrix.SpecialLinearGroup.mapGL ℝ γ•τ := by
    intro τ
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_specialLinearGroup_apply,
      UpperHalfPlane.coe_smul_of_det_pos (by simp)]
    simp [UpperHalfPlane.num,UpperHalfPlane.denom,Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.map,Matrix.of_apply]
  obtain ⟨r,hrZ,hr⟩ := lpsOriginalDilatedAtScaledCuspIntegralShift N hN γ
  have hg := lpsOriginalDilationColumnGcdPos N hN γ
  have hle := Nat.le_of_dvd hN (lpsOriginalDilationColumnGcdDvd N γ)
  refine ⟨_,pow_pos hg 2,r,by nlinarith,hrZ,?_⟩
  intro σ
  rw [←hγ,←ha]
  exact hr σ
abbrev LPSOriginalCuspIndex (N : ℕ) :=
  𝒮ℒ ⧸ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ
lemma lpsOriginalCosetScaledCuspRepresentation
    (N : ℕ) (hN : 0 < N) (x : LPSOriginalCuspIndex N) :
    ∃ m : ℕ, ∃ hm : 0 < m, ∃ r : ℚ,
      m ≤ N^2 ∧ (∃ z : ℤ, (N : ℚ) * r = z) ∧ ∀ σ : ℍ,
      lpsOriginalJDilated N hN (x.out.val⁻¹ • (lpsE2AffineMatrix N hN 0 • σ)) =
        lpsOriginalJInvariant (lpsE2AffineMatrix m hm (r : ℝ) • σ) := by
  simpa only [Subgroup.coe_inv] using
    lpsOriginalSLAtScaledCuspIntegralShift N hN x.out⁻¹
def lpsOriginalCosetCuspWitness
    (N : ℕ) (hN : 0 < N) (x : LPSOriginalCuspIndex N) :
    Σ m : {m : ℕ // 0 < m}, {r : ℚ // m.val ≤ N^2 ∧
      (∃ z : ℤ, (N : ℚ) * r = z) ∧ ∀ σ : ℍ,
      lpsOriginalJDilated N hN (x.out.val⁻¹ • (lpsE2AffineMatrix N hN 0 • σ)) =
        lpsOriginalJInvariant (lpsE2AffineMatrix m.val m.property (r : ℝ) • σ)} := by
  let e := lpsOriginalCosetScaledCuspRepresentation N hN x
  let er := e.choose_spec.choose_spec
  exact ⟨⟨e.choose, e.choose_spec.choose⟩, ⟨er.choose, er.choose_spec⟩⟩
def lpsOriginalCosetCuspData
    (N : ℕ) (hN : 0 < N) (x : LPSOriginalCuspIndex N) : ℕ × ℂ :=
  let w := lpsOriginalCosetCuspWitness N hN x
  (w.1.val, Function.Periodic.qParam 1 (w.2.val : ℂ))
lemma lpsOriginalCosetCuspData_phase_pow
    (N : ℕ) (hN : 0 < N) (x : LPSOriginalCuspIndex N) :
    ((lpsOriginalCosetCuspData N hN x).2)^N = 1 := by
  let w := lpsOriginalCosetCuspWitness N hN x
  exact lpsOriginalLevelNomePhase_pow N w.2.val w.2.property.2.1
def lpsOriginalLevelPhaseRing (N : ℕ) : Subalgebra ℤ ℂ :=
  Algebra.adjoin ℤ {z : ℂ | z^N = 1}
lemma lpsOriginalLevelPhaseRing_integral (N : ℕ) (hN : 0 < N) :
    Algebra.IsIntegral ℤ (lpsOriginalLevelPhaseRing N) := by
  apply Algebra.IsIntegral.adjoin
  intro z hz
  apply IsIntegral.of_pow hN
  rw [hz]
  exact isIntegral_one
def lpsOriginalLevelPhaseElement (N : ℕ) (z : ℂ) (hz : z^N = 1) :
    lpsOriginalLevelPhaseRing N :=
  ⟨z, Algebra.subset_adjoin hz⟩
lemma lpsOriginalLevelPhaseRing_integerMap_injective (N : ℕ) :
    Function.Injective (algebraMap ℤ (lpsOriginalLevelPhaseRing N)) := by
  exact Int.cast_injective
lemma lpsOriginalLevelPhaseRing_maximalOverPrime
    (N : ℕ) (hN : 0 < N) (p : ℕ) (hp : p.Prime) :
    ∃ Q : Ideal (lpsOriginalLevelPhaseRing N), Q.IsMaximal ∧
      Q.comap (algebraMap ℤ (lpsOriginalLevelPhaseRing N)) =
        RingHom.ker (Int.castRingHom (ZMod p)) := by
  let : Fact p.Prime := ⟨hp⟩
  let I := RingHom.ker (Int.castRingHom (ZMod p))
  let : I.IsMaximal := RingHom.ker_isMaximal_of_surjective
    (Int.castRingHom (ZMod p)) ZMod.intCast_surjective
  let : Algebra.IsIntegral ℤ (lpsOriginalLevelPhaseRing N) :=
    lpsOriginalLevelPhaseRing_integral N hN
  apply Ideal.exists_ideal_over_maximal_of_isIntegral I
  rw [(RingHom.injective_iff_ker_eq_bot _).mp (lpsOriginalLevelPhaseRing_integerMap_injective N)]
  exact bot_le
def lpsOriginalLevelPhasePrime
    (N : ℕ) (hN : 0 < N) (p : ℕ) (hp : p.Prime) :
    Ideal (lpsOriginalLevelPhaseRing N) :=
  (lpsOriginalLevelPhaseRing_maximalOverPrime N hN p hp).choose
local instance lpsOriginalLevelPhasePrime_isMaximal
    (N : ℕ) (hN : 0 < N) (p : ℕ) (hp : p.Prime) :
    (lpsOriginalLevelPhasePrime N hN p hp).IsMaximal :=
  (lpsOriginalLevelPhaseRing_maximalOverPrime N hN p hp).choose_spec.1
abbrev LPSOriginalLevelPhaseResidue
    (N : ℕ) (hN : 0 < N) (p : ℕ) (hp : p.Prime) :=
  lpsOriginalLevelPhaseRing N ⧸ lpsOriginalLevelPhasePrime N hN p hp
local instance lpsOriginalLevelPhaseResidue_field
    (N : ℕ) (hN : 0 < N) (p : ℕ) (hp : p.Prime) :
    Field (LPSOriginalLevelPhaseResidue N hN p hp) :=
  Ideal.Quotient.field (lpsOriginalLevelPhasePrime N hN p hp)
def lpsOriginalLevelPrimitivePhase (N : ℕ) (hN : 0 < N) :
    lpsOriginalLevelPhaseRing N :=
  lpsOriginalLevelPhaseElement N (Complex.exp (2 * Real.pi * I / N))
    (Complex.isPrimitiveRoot_exp N hN.ne').pow_eq_one
def lpsOriginalCosetPhaseElement
    (N : ℕ) (hN : 0 < N) (x : LPSOriginalCuspIndex N) :
    lpsOriginalLevelPhaseRing N :=
  lpsOriginalLevelPhaseElement N (lpsOriginalCosetCuspData N hN x).2
    (lpsOriginalCosetCuspData_phase_pow N hN x)
def lpsOriginalCosetCuspResidueData
    (N : ℕ) (hN : 0 < N) (p : ℕ) (hp : p.Prime)
    (x : LPSOriginalCuspIndex N) :
    ℕ × LPSOriginalLevelPhaseResidue N hN p hp :=
  ((lpsOriginalCosetCuspData N hN x).1,
    Ideal.Quotient.mk (lpsOriginalLevelPhasePrime N hN p hp)
      (lpsOriginalCosetPhaseElement N hN x))
end
end QEC.Coding.TannerLiftedProduct


