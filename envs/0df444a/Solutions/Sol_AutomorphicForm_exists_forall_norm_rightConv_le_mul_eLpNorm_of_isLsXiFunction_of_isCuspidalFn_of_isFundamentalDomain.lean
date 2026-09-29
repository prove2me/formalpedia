-- Prove2me | solution 1 for AutomorphicForm.exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCuspidalFn_of_isFundamentalDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/ed892607-3432-521b-a749-c17b08d163ce

import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_TateGlobalZeta

import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_NumberField_AdelicVolume
import Theorems.Thm_AutomorphicForm_isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply
import Theorems.Thm_AutomorphicForm_norm_integral_mul_le_mul_setIntegral_norm_of_isCuspidalFn
import Theorems.Thm_AutomorphicForm_norm_tsum_sub_average_le_mul_inv_archHeight_pow_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_WindowedSiegel_isCompact_centreCutSiegelSet_inter_heightCap
import Theorems.Thm_AutomorphicForm_exists_forall_setLIntegral_nnnorm_sq_le_mul_archHeight_pow_mul_setLIntegral_of_isLsXiFunction_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_AdeleRing_finite_setOf_algebraMap_mem_of_isCompact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCuspidalFn_of_isFundamentalDomain
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply"
p2m_attr_erase "simp" "NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"
set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering MeasureTheory

open scoped ProbabilityTheory

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
open scoped ENNReal NNReal
open NumberField.TateGlobal
open scoped Pointwise
open NumberField.AdelicVolume

attribute [local instance] NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace UniformSupOverFundamentalDomain

private theorem globalPoints_unipotentGL2 (K : Type) [Field K] [NumberField K] (k : K) :
    globalPoints (𝓞 K) K (unipotentGL2 k) = unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) k) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change algebraMap K (AdeleRing (𝓞 K) K) ((unipotentGL2 k : Matrix (Fin 2) (Fin 2) K) i j)
    = (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) k) : Matrix (Fin 2) (Fin 2) _) i j
  rw [unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

private theorem h0_bound (K : Type) [Field K] [NumberField K]
    (c' u' d₁' d₂' : ℝ) (hc' : 0 < c') (T₀ : ℝ) :
    ∃ Ccap : ℝ, ∀ s ∈ centreCutSiegelSet K c' u' d₁' d₂',
      (∃ w : InfinitePlace K, Ccap < localHeight (archComponent K w (glArch (𝓞 K) K s))) →
        T₀ < archHeight K (glArch (𝓞 K) K s) := by
  set m : ℝ := min 1 c' with hm
  have hm0 : 0 < m := lt_min one_pos hc'
  have hm1 : m ≤ 1 := min_le_left _ _
  set P : ℝ := ∏ v : InfinitePlace K, m ^ v.mult with hP
  have hP0 : 0 < P := Finset.prod_pos fun v _ => pow_pos hm0 _
  refine ⟨max 1 ((|T₀| + 1) / P), fun s hs hw => ?_⟩
  obtain ⟨w, hw⟩ := hw
  have hs' := mem_centreCutSiegelSet_iff.mp hs
  have hlow : ∀ v : InfinitePlace K, m ≤ localHeight (archComponent K v (glArch (𝓞 K) K s)) :=
    fun v => (min_le_right _ _).trans (hs'.2.1 v)
  have hlw1 : 1 ≤ localHeight (archComponent K w (glArch (𝓞 K) K s)) := (le_max_left _ _).trans hw.le

  have hprod : localHeight (archComponent K w (glArch (𝓞 K) K s)) * P
      ≤ archHeight K (glArch (𝓞 K) K s) := by
    classical
    have hEq : localHeight (archComponent K w (glArch (𝓞 K) K s)) * P
        = ∏ v : InfinitePlace K, (m ^ v.mult *
            if v = w then localHeight (archComponent K w (glArch (𝓞 K) K s)) else 1) := by
      rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ w, if_pos (Finset.mem_univ w), mul_comm]
    rw [hEq]
    show _ ≤ ∏ v : InfinitePlace K, localHeight (archComponent K v (glArch (𝓞 K) K s)) ^ v.mult
    refine Finset.prod_le_prod (fun v _ => ?_) (fun v _ => ?_)
    · refine mul_nonneg (pow_nonneg hm0.le _) ?_
      split_ifs
      · exact zero_le_one.trans hlw1
      · exact zero_le_one
    · split_ifs with hv
      · subst hv
        calc m ^ v.mult * localHeight (archComponent K v (glArch (𝓞 K) K s))
            ≤ 1 ^ v.mult * localHeight (archComponent K v (glArch (𝓞 K) K s)) :=
              mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hm0.le hm1 _) (zero_le_one.trans hlw1)
          _ = localHeight (archComponent K v (glArch (𝓞 K) K s)) ^ 1 := by rw [one_pow, one_mul, pow_one]
          _ ≤ localHeight (archComponent K v (glArch (𝓞 K) K s)) ^ v.mult :=
              pow_le_pow_right₀ hlw1 NumberField.InfinitePlace.mult_pos
      · rw [mul_one]
        exact pow_le_pow_left₀ hm0.le (hlow v) _
  have hT : |T₀| + 1 ≤ localHeight (archComponent K w (glArch (𝓞 K) K s)) * P := by
    have h1 : (|T₀| + 1) / P ≤ localHeight (archComponent K w (glArch (𝓞 K) K s)) :=
      (le_max_right _ _).trans hw.le
    rwa [div_le_iff₀ hP0] at h1
  calc T₀ ≤ |T₀| := le_abs_self _
    _ < |T₀| + 1 := lt_add_one _
    _ ≤ _ := hT.trans hprod

private theorem r1_loc_unipotentGL2_apply {L : Type*} [NormedField L] (t : L) :
    ((unipotentGL2 t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 = 1 ∧
    ((unipotentGL2 t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 1 = t ∧
    ((unipotentGL2 t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
    ((unipotentGL2 t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 :=
  ⟨by rw [unipotentGL2_coe]; rfl, by rw [unipotentGL2_coe]; rfl,
    by rw [unipotentGL2_coe]; rfl, by rw [unipotentGL2_coe]; rfl⟩

private theorem r1_loc_conj_sub_one_apply {L : Type*} [NormedField L] (g : GL (Fin 2) L) (t : L)
    (i j : Fin 2) :
    ((g⁻¹ * unipotentGL2 t * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j
        - (1 : Matrix (Fin 2) (Fin 2) L) i j
      = t * ((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i 0
          * (g : Matrix (Fin 2) (Fin 2) L) 1 j := by
  obtain ⟨hN00, hN01, hN10, hN11⟩ := r1_loc_unipotentGL2_apply (L := L) t
  have hval : ((g⁻¹ * unipotentGL2 t * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
      = ((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
          * ((unipotentGL2 t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
          * (g : Matrix (Fin 2) (Fin 2) L) := by
    rw [Units.val_mul, Units.val_mul]
  have hone : (1 : Matrix (Fin 2) (Fin 2) L)
      = ((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) * (g : Matrix (Fin 2) (Fin 2) L) :=
    (Units.inv_mul g).symm
  rw [hval, hone]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, hN00, hN01, hN10, hN11]
  ring

private theorem r1_loc_norm_inv_apply_zero {L : Type*} [NormedField L] (g : GL (Fin 2) L)
    (i : Fin 2) :
    ‖((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i 0‖
      = ‖(g : Matrix (Fin 2) (Fin 2) L).det‖⁻¹ * ‖(g : Matrix (Fin 2) (Fin 2) L).adjugate i 0‖ := by
  have hcoe : ((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
      = ((g : Matrix (Fin 2) (Fin 2) L))⁻¹ := Matrix.coe_units_inv g
  rw [hcoe, Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, norm_smul, norm_inv]

private theorem r1_loc_real_bound {T D x y R : ℝ} (hT : 0 ≤ T) (hD : 0 < D) (hxy : x * y ≤ R) :
    T * (D⁻¹ * x) * y ≤ T / (D / R) := by
  rw [div_div_eq_mul_div, le_div_iff₀ hD]
  calc T * (D⁻¹ * x) * y * D = T * (x * y) * (D⁻¹ * D) := by ring
    _ = T * (x * y) := by rw [inv_mul_cancel₀ hD.ne', mul_one]
    _ ≤ T * R := mul_le_mul_of_nonneg_left hxy hT

private theorem r1_norm_conj_unipotentGL2_sub_one_apply_le {L : Type*} [NormedField L]
    (g : GL (Fin 2) L) (t : L) (i j : Fin 2) :
    ‖((g⁻¹ * unipotentGL2 t * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j
        - (1 : Matrix (Fin 2) (Fin 2) L) i j‖ ≤ ‖t‖ / localHeight g := by
  have hdet0 : (g : Matrix (Fin 2) (Fin 2) L).det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero g
  have hdetpos : 0 < ‖(g : Matrix (Fin 2) (Fin 2) L).det‖ := by
    rw [norm_pos_iff]
    exact hdet0
  have hA := sq_nonneg (‖(g : Matrix (Fin 2) (Fin 2) L) 1 0‖ - ‖(g : Matrix (Fin 2) (Fin 2) L) 1 1‖)
  have hB := sq_nonneg ‖(g : Matrix (Fin 2) (Fin 2) L) 1 0‖
  have hC := sq_nonneg ‖(g : Matrix (Fin 2) (Fin 2) L) 1 1‖
  rw [r1_loc_conj_sub_one_apply g t i j, norm_mul, norm_mul, r1_loc_norm_inv_apply_zero g i]
  refine r1_loc_real_bound (norm_nonneg t) hdetpos ?_
  rw [Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j
  · show ‖(g : Matrix (Fin 2) (Fin 2) L) 1 1‖ * ‖(g : Matrix (Fin 2) (Fin 2) L) 1 0‖
      ≤ ‖(g : Matrix (Fin 2) (Fin 2) L) 1 0‖ ^ 2 + ‖(g : Matrix (Fin 2) (Fin 2) L) 1 1‖ ^ 2
    nlinarith [hA, hB, hC]
  · show ‖(g : Matrix (Fin 2) (Fin 2) L) 1 1‖ * ‖(g : Matrix (Fin 2) (Fin 2) L) 1 1‖
      ≤ ‖(g : Matrix (Fin 2) (Fin 2) L) 1 0‖ ^ 2 + ‖(g : Matrix (Fin 2) (Fin 2) L) 1 1‖ ^ 2
    nlinarith [hA, hB, hC]
  · show ‖-(g : Matrix (Fin 2) (Fin 2) L) 1 0‖ * ‖(g : Matrix (Fin 2) (Fin 2) L) 1 0‖
      ≤ ‖(g : Matrix (Fin 2) (Fin 2) L) 1 0‖ ^ 2 + ‖(g : Matrix (Fin 2) (Fin 2) L) 1 1‖ ^ 2
    rw [norm_neg]
    nlinarith [hA, hB, hC]
  · show ‖-(g : Matrix (Fin 2) (Fin 2) L) 1 0‖ * ‖(g : Matrix (Fin 2) (Fin 2) L) 1 1‖
      ≤ ‖(g : Matrix (Fin 2) (Fin 2) L) 1 0‖ ^ 2 + ‖(g : Matrix (Fin 2) (Fin 2) L) 1 1‖ ^ 2
    rw [norm_neg]
    nlinarith [hA, hB, hC]

private theorem r1_norm_conj_unipotentGL2_apply_le {L : Type*} [NormedField L]
    (g : GL (Fin 2) L) (t : L) {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) (hcg : c ≤ localHeight g) (ht : ‖t‖ ≤ r) (i j : Fin 2) :
    ‖((g⁻¹ * unipotentGL2 t * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j‖ ≤ 1 + r / c := by
  have hsub := r1_norm_conj_unipotentGL2_sub_one_apply_le g t i j
  have hone : ‖(1 : Matrix (Fin 2) (Fin 2) L) i j‖ ≤ 1 := by
    rw [Matrix.one_apply]
    split_ifs
    · exact norm_one.le
    · exact norm_zero.trans_le zero_le_one
  have hdiv : ‖t‖ / localHeight g ≤ r / c := div_le_div₀ hr ht hc hcg
  calc ‖((g⁻¹ * unipotentGL2 t * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j‖
      = ‖(((g⁻¹ * unipotentGL2 t * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j
          - (1 : Matrix (Fin 2) (Fin 2) L) i j) + (1 : Matrix (Fin 2) (Fin 2) L) i j‖ := by
        rw [sub_add_cancel]
    _ ≤ ‖((g⁻¹ * unipotentGL2 t * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j
          - (1 : Matrix (Fin 2) (Fin 2) L) i j‖ + ‖(1 : Matrix (Fin 2) (Fin 2) L) i j‖ :=
        norm_add_le _ _
    _ ≤ r / c + 1 := add_le_add (hsub.trans hdiv) hone
    _ = 1 + r / c := add_comm _ _

private theorem r1_unipotentGL2_inv {R : Type*} [CommRing R] (x : R) :
    (unipotentGL2 x)⁻¹ = unipotentGL2 (-x) :=
  inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])

section Adelic

variable (K : Type) [Field K] [NumberField K]

private theorem r1_archComponent_glArch_unipotentGL2 (w : InfinitePlace K) (b : AdeleRing (𝓞 K) K) :
    archComponent K w (glArch (𝓞 K) K (unipotentGL2 b)) = unipotentGL2 (b.1 w) := by
  ext i j
  rw [archComponent_apply, glArch_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> rfl

private theorem r1_arch_entry_norm_le {c' u' d₁' d₂' rB : ℝ} (hc' : 0 < c') (hrB : 0 ≤ rB)
    {s : GL (Fin 2) (AdeleRing (𝓞 K) K)} (hs : s ∈ centreCutSiegelSet K c' u' d₁' d₂')
    {b : AdeleRing (𝓞 K) K} (hb : ∀ w : InfinitePlace K, ‖b.1 w‖ ≤ rB)
    (w : InfinitePlace K) (i j : Fin 2) :
    ‖(((s⁻¹ * unipotentGL2 b * s : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).1 w‖ ≤ 1 + rB / c' := by
  have hlh : c' ≤ localHeight (archComponent K w (glArch (𝓞 K) K s)) :=
    (mem_centreCutSiegelSet_iff.mp hs).2.1 w
  have hconj : archComponent K w (glArch (𝓞 K) K (s⁻¹ * unipotentGL2 b * s))
      = (archComponent K w (glArch (𝓞 K) K s))⁻¹ * unipotentGL2 (b.1 w)
          * archComponent K w (glArch (𝓞 K) K s) := by
    simp only [map_mul, map_inv, r1_archComponent_glArch_unipotentGL2]
  have hentry : (((s⁻¹ * unipotentGL2 b * s : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).1 w
      = (archComponent K w (glArch (𝓞 K) K (s⁻¹ * unipotentGL2 b * s)) :
          Matrix (Fin 2) (Fin 2) w.Completion) i j := rfl
  rw [hentry, hconj]
  exact r1_norm_conj_unipotentGL2_apply_le _ _ hc' hrB hlh (hb w) i j

private theorem r1_glFin_unipotentGL2_mem {b : AdeleRing (𝓞 K) K}
    (hb : b.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K) :
    glFin (𝓞 K) K (unipotentGL2 b) ∈ finiteIntegralGL2 (𝓞 K) K := by
  have hneg : (-b).2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
    rw [show (-b).2 = -b.2 from rfl, neg_eq_zero_sub]
    exact AdelicLevel.sub_mem_integralFiniteAdeles AdelicLevel.zero_mem_integralFiniteAdeles hb
  rw [mem_finiteIntegralGL2_iff, ← map_inv, r1_unipotentGL2_inv]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [glFin_apply, unipotentGL2_coe]
    fin_cases i <;> fin_cases j
    · exact AdelicLevel.one_mem_integralFiniteAdeles
    · exact hb
    · exact AdelicLevel.zero_mem_integralFiniteAdeles
    · exact AdelicLevel.one_mem_integralFiniteAdeles
  · rw [glFin_apply, unipotentGL2_coe]
    fin_cases i <;> fin_cases j
    · exact AdelicLevel.one_mem_integralFiniteAdeles
    · exact hneg
    · exact AdelicLevel.zero_mem_integralFiniteAdeles
    · exact AdelicLevel.one_mem_integralFiniteAdeles

private theorem r1_fin_entry_mem {s : GL (Fin 2) (AdeleRing (𝓞 K) K)}
    (hs : glFin (𝓞 K) K s ∈ finiteIntegralGL2 (𝓞 K) K) {b : AdeleRing (𝓞 K) K}
    (hb : b.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K) (i j : Fin 2) :
    (((s⁻¹ * unipotentGL2 b * s : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2
      ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
  have hm : glFin (𝓞 K) K (s⁻¹ * unipotentGL2 b * s) ∈ finiteIntegralGL2 (𝓞 K) K := by
    rw [map_mul, map_mul, map_inv]
    exact mul_mem (mul_mem (inv_mem hs) (r1_glFin_unipotentGL2_mem K hb)) hs
  have h := (mem_finiteIntegralGL2_iff.mp hm).1 i j
  rwa [glFin_apply] at h

private theorem r1_isCompact_closure_box : IsCompact (closure (adelicBox K)) := by
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_adelicBox_subset K
  exact hC.closure_of_subset hsub

private theorem r1_exists_box_bound :
    ∃ rB : ℝ, 0 ≤ rB ∧ ∀ b ∈ closure (adelicBox K), ∀ w : InfinitePlace K, ‖b.1 w‖ ≤ rB := by
  have hcont : Continuous fun b : AdeleRing (𝓞 K) K => ∑ w : InfinitePlace K, ‖b.1 w‖ :=
    continuous_finsetSum _ fun w _ => ((continuous_archEval K w).comp continuous_fst).norm
  obtain ⟨r, hr⟩ := (r1_isCompact_closure_box K).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max r 0, le_max_right _ _, fun b hb w => ?_⟩
  refine le_trans (Finset.single_le_sum (f := fun v : InfinitePlace K => ‖b.1 v‖)
    (fun v _ => norm_nonneg _) (Finset.mem_univ w)) ?_
  exact ((le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hr b hb))).trans (le_max_left _ _)

private theorem r1_snd_mem_of_mem_closure_box {b : AdeleRing (𝓞 K) K}
    (hb : b ∈ closure (adelicBox K)) : b.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
  have hcl : IsClosed {y : AdeleRing (𝓞 K) K | y.2 ∈ AdelicBox.integralFiniteAdeles (𝓞 K) K} :=
    (AdelicBox.isClosed_integralFiniteAdeles K).preimage continuous_snd
  exact closure_minimal (fun y hy => hy.2) hcl hb

private def r1_adeleBall (r : ℝ) : Set (AdeleRing (𝓞 K) K) :=
  {y | (∀ w : InfinitePlace K, ‖y.1 w‖ ≤ r) ∧ y.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K}

private theorem r1_mem_adeleBall {r : ℝ} {y : AdeleRing (𝓞 K) K} :
    y ∈ r1_adeleBall K r ↔
      (∀ w : InfinitePlace K, ‖y.1 w‖ ≤ r) ∧ y.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K :=
  Iff.rfl

private theorem r1_isCompact_adeleBall (r : ℝ) : IsCompact (r1_adeleBall K r) := by
  haveI : ∀ v : InfinitePlace K, ProperSpace v.Completion := fun v =>
    NumberField.AdelicBox.properSpace_completion K v
  have hS : IsCompact {x : InfiniteAdeleRing K | ∀ v, ‖x v‖ ≤ r} := by
    have : {x : InfiniteAdeleRing K | ∀ v, ‖x v‖ ≤ r} =
        Set.pi Set.univ fun v : InfinitePlace K => Metric.closedBall (0 : v.Completion) r := by
      ext x
      exact ⟨fun h v _ => mem_closedBall_zero_iff.mpr (h v),
        fun h v => mem_closedBall_zero_iff.mp (h v (Set.mem_univ v))⟩
    rw [this]
    exact isCompact_univ_pi fun v => isCompact_closedBall (0 : v.Completion) r
  have : IsCompact ({x : InfiniteAdeleRing K | ∀ v, ‖x v‖ ≤ r} ×ˢ
      AdelicLevel.integralFiniteAdeles (𝓞 K) K) :=
    hS.prod (AdelicLevel.isCompact_integralFiniteAdeles (𝓞 K) K)
  exact this

private def r1_matBall (r : ℝ) : Set (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) :=
  Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 => r1_adeleBall K r

private def r1_Omega (r : ℝ) : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)) :=
  Units.embedProduct (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) ⁻¹'
    (r1_matBall K r ×ˢ (MulOpposite.op '' r1_matBall K r))

private theorem r1_isCompact_Omega (r : ℝ) : IsCompact (r1_Omega K r) := by
  have hM : IsCompact (r1_matBall K r) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => r1_isCompact_adeleBall K r
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage
    (hM.prod (hM.image MulOpposite.continuous_op))

private theorem r1_mem_Omega {r : ℝ} {m : GL (Fin 2) (AdeleRing (𝓞 K) K)}
    (h₁ : ∀ i j, (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j ∈ r1_adeleBall K r)
    (h₂ : ∀ i j, ((m⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j ∈ r1_adeleBall K r) :
    m ∈ r1_Omega K r := by
  rw [r1_Omega, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod]
  exact ⟨Set.mem_univ_pi.mpr fun i => Set.mem_univ_pi.mpr fun j => h₁ i j,
    ⟨((m⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)),
      Set.mem_univ_pi.mpr fun i => Set.mem_univ_pi.mpr fun j => h₂ i j, rfl⟩⟩

private theorem r1_conj_mem_Omega {c' u' d₁' d₂' rB : ℝ} (hc' : 0 < c') (hrB : 0 ≤ rB)
    {s : GL (Fin 2) (AdeleRing (𝓞 K) K)} (hs : s ∈ centreCutSiegelSet K c' u' d₁' d₂')
    {b : AdeleRing (𝓞 K) K} (hb₁ : ∀ w : InfinitePlace K, ‖b.1 w‖ ≤ rB)
    (hb₂ : b.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K) :
    s⁻¹ * unipotentGL2 b * s ∈ r1_Omega K (1 + rB / c') := by
  have hs₁ : glFin (𝓞 K) K s ∈ finiteIntegralGL2 (𝓞 K) K := (mem_centreCutSiegelSet_iff.mp hs).1
  have hnb₁ : ∀ w : InfinitePlace K, ‖(-b).1 w‖ ≤ rB := fun w => by
    rw [show (-b).1 w = -(b.1 w) from rfl, norm_neg]
    exact hb₁ w
  have hnb₂ : (-b).2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
    rw [show (-b).2 = -b.2 from rfl, neg_eq_zero_sub]
    exact AdelicLevel.sub_mem_integralFiniteAdeles AdelicLevel.zero_mem_integralFiniteAdeles hb₂
  have hinv : (s⁻¹ * unipotentGL2 b * s)⁻¹ = s⁻¹ * unipotentGL2 (-b) * s := by
    simp only [mul_inv_rev, inv_inv, r1_unipotentGL2_inv, mul_assoc]
  refine r1_mem_Omega K (fun i j => (r1_mem_adeleBall K).mpr ⟨fun w => ?_, ?_⟩)
    (fun i j => (r1_mem_adeleBall K).mpr ?_)
  · exact r1_arch_entry_norm_le K hc' hrB hs hb₁ w i j
  · exact r1_fin_entry_mem K hs₁ hb₂ i j
  · rw [hinv]
    exact ⟨fun w => r1_arch_entry_norm_le K hc' hrB hs hnb₁ w i j, r1_fin_entry_mem K hs₁ hnb₂ i j⟩

private theorem r1_exists_absorbing {c' u' d₁' d₂' : ℝ} (hc' : 0 < c')
    {C : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hC : IsCompact C) :
    ∃ E : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)), IsCompact E ∧
      ∀ s ∈ centreCutSiegelSet K c' u' d₁' d₂',
        Set.image2 (fun (t : AdeleRing (𝓞 K) K) (c : GL (Fin 2) (AdeleRing (𝓞 K) K)) =>
            unipotentGL2 t * s * c) (closure (adelicBox K)) C
          ⊆ (fun y => s * y) '' E := by
  obtain ⟨rB, hrB, hbox⟩ := r1_exists_box_bound K
  refine ⟨Set.image2 (fun m c => m * c) (r1_Omega K (1 + rB / c')) C, ?_, fun s hs x hx => ?_⟩
  · rw [← Set.image_prod]
    exact ((r1_isCompact_Omega K _).prod hC).image (continuous_fst.mul continuous_snd)
  · obtain ⟨b, hb, c, hc, rfl⟩ := Set.mem_image2.mp hx
    refine ⟨s⁻¹ * unipotentGL2 b * s * c, Set.mem_image2_of_mem
      (r1_conj_mem_Omega K hc' hrB hs (hbox b hb) (r1_snd_mem_of_mem_closure_box K hb)) hc, ?_⟩
    show s * (s⁻¹ * unipotentGL2 b * s * c) = unipotentGL2 b * s * c
    simp only [← mul_assoc, mul_inv_cancel, one_mul]

end Adelic

private theorem r1_bound (K : Type) [Field K] [NumberField K]
    (c' u' d₁' d₂' : ℝ) (hc' : 0 < c')
    {C : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hC : IsCompact C) :
    ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ s ∈ centreCutSiegelSet K c' u' d₁' d₂',
      adelicGLHaar (Fin 2) (𝓞 K) K
          (Set.image2 (fun (t : AdeleRing (𝓞 K) K) (c : GL (Fin 2) (AdeleRing (𝓞 K) K)) =>
            unipotentGL2 t * s * c) (closure (adelicBox K)) C)
        ≤ ENNReal.ofReal M₀ := by
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  obtain ⟨E, hE, hsub⟩ := r1_exists_absorbing K (u' := u') (d₁' := d₁') (d₂' := d₂') hc' hC
  have hEtop : adelicGLHaar (Fin 2) (𝓞 K) K E ≠ ⊤ := hE.measure_lt_top.ne
  refine ⟨(adelicGLHaar (Fin 2) (𝓞 K) K E).toReal, ENNReal.toReal_nonneg, fun s hs => ?_⟩
  rw [ENNReal.ofReal_toReal hEtop]
  calc adelicGLHaar (Fin 2) (𝓞 K) K
        (Set.image2 (fun (t : AdeleRing (𝓞 K) K) (c : GL (Fin 2) (AdeleRing (𝓞 K) K)) =>
          unipotentGL2 t * s * c) (closure (adelicBox K)) C)
      ≤ adelicGLHaar (Fin 2) (𝓞 K) K ((fun y => s * y) '' E) := measure_mono (hsub s hs)
    _ = adelicGLHaar (Fin 2) (𝓞 K) K E := by
        rw [Set.image_mul_left, measure_preimage_mul]

private theorem cs_bound (K : Type) [Field K] [NumberField K]
    (φ g : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (s : GL (Fin 2) (AdeleRing (𝓞 K) K))
    (W R : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))
    (CN M M₀ H : ℝ) (A : ℕ) (hM₀ : 0 ≤ M₀) (hH : 1 ≤ H)
    (hcont : Continuous φ) (hL2 : MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict W))
    (hU : ‖∫ y, φ y * g (s⁻¹ * y) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)‖
      ≤ CN * H⁻¹ ^ A * ∫ y in R, ‖φ y‖ ∂(adelicGLHaar (Fin 2) (𝓞 K) K))
    (hL1 : ∫⁻ y in R, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      ≤ ENNReal.ofReal (M * H ^ A) *
        ∫⁻ y in W, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K))
    (hμR : adelicGLHaar (Fin 2) (𝓞 K) K R ≤ ENNReal.ofReal M₀) :
    ‖∫ y, φ y * g (s⁻¹ * y) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)‖
      ≤ |CN| * Real.sqrt M₀ * Real.sqrt (|M| *
        (∫⁻ y in W, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)).toReal) := by

  set IW : ℝ≥0∞ := ∫⁻ y in W, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) with hIW
  set IR : ℝ≥0∞ := ∫⁻ y in R, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) with hIR
  have hH0 : 0 < H := lt_of_lt_of_le one_pos hH
  have hHA : 0 ≤ H⁻¹ ^ A := pow_nonneg (inv_nonneg.mpr hH0.le) A

  have hIW_top : IW ≠ ⊤ := by
    have h2 := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (two_ne_zero)
      (ENNReal.ofNat_ne_top (n := 2)) hL2.eLpNorm_lt_top
    have hEq : IW = ∫⁻ y in W, ‖φ y‖ₑ ^ (2 : ℝ≥0∞).toReal ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
      rw [hIW, ENNReal.toReal_ofNat]
      refine lintegral_congr fun y => ?_
      rw [ENNReal.rpow_two, enorm_eq_nnnorm]
    rw [hEq]
    exact h2.ne

  have hIR_le : IR ≤ ENNReal.ofReal (|M| * H ^ A) * IW :=
    hL1.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_abs_self M) (pow_nonneg hH0.le A))) le_rfl)
  have hprod_top : ENNReal.ofReal (|M| * H ^ A) * IW ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hIW_top
  have hIR_top : IR ≠ ⊤ := ne_top_of_le_ne_top hprod_top hIR_le
  have hIR_real : IR.toReal ≤ |M| * H ^ A * IW.toReal := by
    have h := ENNReal.toReal_mono hprod_top hIR_le
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h

  have hmeas : AEMeasurable (fun y => (‖φ y‖₊ : ℝ≥0∞)) ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict R) :=
    (hcont.enorm).measurable.aemeasurable
  have hCS : ∫⁻ y in R, (‖φ y‖₊ : ℝ≥0∞) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      ≤ (adelicGLHaar (Fin 2) (𝓞 K) K R) ^ (1 / (2 : ℝ)) * IR ^ (1 / (2 : ℝ)) := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict R)
      Real.HolderConjugate.two_two (f := fun _ => (1 : ℝ≥0∞)) (g := fun y => (‖φ y‖₊ : ℝ≥0∞))
      aemeasurable_const hmeas
    simp only [Pi.mul_apply, one_mul, ENNReal.rpow_two, one_pow, lintegral_const,
      Measure.restrict_apply_univ] at h
    rw [hIR]
    exact h

  have hJ : ∫ y in R, ‖φ y‖ ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      = (∫⁻ y in R, (‖φ y‖₊ : ℝ≥0∞) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun y => norm_nonneg _)
      hcont.norm.aestronglyMeasurable]
    congr 1
    refine lintegral_congr fun y => ?_
    rw [ofReal_norm, enorm_eq_nnnorm]
  have hμR_real : (adelicGLHaar (Fin 2) (𝓞 K) K R).toReal ≤ M₀ := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hμR
    rwa [ENNReal.toReal_ofReal hM₀] at h
  have hμR_top : adelicGLHaar (Fin 2) (𝓞 K) K R ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hμR
  have hJ_le : ∫ y in R, ‖φ y‖ ∂(adelicGLHaar (Fin 2) (𝓞 K) K) ≤ Real.sqrt M₀ * Real.sqrt IR.toReal := by
    rw [hJ]
    have hfin : (adelicGLHaar (Fin 2) (𝓞 K) K R) ^ (1 / (2 : ℝ)) * IR ^ (1 / (2 : ℝ)) ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hμR_top)
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hIR_top)
    have h := ENNReal.toReal_mono hfin hCS
    rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow, ← Real.sqrt_eq_rpow,
      ← Real.sqrt_eq_rpow] at h
    exact h.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hμR_real) (Real.sqrt_nonneg _))

  have hx0 : 0 ≤ H⁻¹ ^ A * Real.sqrt (H ^ A) := mul_nonneg hHA (Real.sqrt_nonneg _)
  have hsq : (H⁻¹ ^ A * Real.sqrt (H ^ A)) ^ 2 = H⁻¹ ^ A := by
    rw [mul_pow, Real.sq_sqrt (pow_nonneg hH0.le A), ← pow_mul, mul_two, pow_add, mul_assoc,
      ← mul_pow, inv_mul_cancel₀ hH0.ne', one_pow, mul_one]
  have hsq1 : (H⁻¹ ^ A * Real.sqrt (H ^ A)) ^ 2 ≤ 1 := by
    rw [hsq]
    exact pow_le_one₀ (inv_nonneg.mpr hH0.le) (inv_le_one_of_one_le₀ hH)
  have hx1 : H⁻¹ ^ A * Real.sqrt (H ^ A) ≤ 1 := (pow_le_one_iff_of_nonneg hx0 two_ne_zero).mp hsq1

  have hJ0 : 0 ≤ ∫ y in R, ‖φ y‖ ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := integral_nonneg fun _ => norm_nonneg _
  have hpre : 0 ≤ |CN| * Real.sqrt M₀ * Real.sqrt (|M| * IW.toReal) :=
    mul_nonneg (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  calc ‖∫ y, φ y * g (s⁻¹ * y) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)‖
      ≤ CN * H⁻¹ ^ A * ∫ y in R, ‖φ y‖ ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := hU
    _ ≤ |CN| * H⁻¹ ^ A * (Real.sqrt M₀ * Real.sqrt IR.toReal) :=
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self CN) hHA) hJ0).trans
          (mul_le_mul_of_nonneg_left hJ_le (mul_nonneg (abs_nonneg _) hHA))
    _ ≤ |CN| * H⁻¹ ^ A * (Real.sqrt M₀ * Real.sqrt (|M| * H ^ A * IW.toReal)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hIR_real)
          (Real.sqrt_nonneg _)) (mul_nonneg (abs_nonneg _) hHA)
    _ = |CN| * Real.sqrt M₀ * Real.sqrt (|M| * IW.toReal) * (H⁻¹ ^ A * Real.sqrt (H ^ A)) := by
        rw [show |M| * H ^ A * IW.toReal = H ^ A * (|M| * IW.toReal) by ring,
          Real.sqrt_mul (pow_nonneg hH0.le A)]
        ring
    _ ≤ |CN| * Real.sqrt M₀ * Real.sqrt (|M| * IW.toReal) * 1 :=
        mul_le_mul_of_nonneg_left hx1 hpre
    _ = |CN| * Real.sqrt M₀ * Real.sqrt (|M| * IW.toReal) := mul_one _

private theorem seam_bound (K : Type) [Field K] [NumberField K]
    (φ : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (W : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))) :
    Real.sqrt ((∫⁻ y in W, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)).toReal)
      = (eLpNorm φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict W)).toReal := by
  have h2 : (2 : ℝ≥0∞).toReal = 2 := ENNReal.toReal_ofNat 2
  have hint : (∫⁻ y in W, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K))
      = ∫⁻ y in W, ‖φ y‖ₑ ^ (2 : ℝ) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
    lintegral_congr fun y => by rw [ENNReal.rpow_two, enorm_eq_nnnorm]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top, h2,
    ← ENNReal.toReal_rpow, Real.sqrt_eq_rpow, hint]

private theorem lowcs_bound (K : Type) [Field K] [NumberField K]
    (φ f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (g : GL (Fin 2) (AdeleRing (𝓞 K) K))
    (R W : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))) (B N : ℝ)
    (hB : ∀ y, ‖f y‖ ≤ B) (hfc : Continuous f) (hfs : HasCompactSupport f)
    (hcont : Continuous φ) (hL2 : MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict W))
    (hsub : (fun y => g * y) '' tsupport f ⊆ R)
    (hLOW : ∫⁻ y in R, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      ≤ ENNReal.ofReal N * ∫⁻ y in W, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) :
    ‖rightConv K φ f g‖
      ≤ B * Real.sqrt ((adelicGLHaar (Fin 2) (𝓞 K) K (tsupport f)).toReal) * Real.sqrt (|N| *
        (∫⁻ y in W, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)).toReal) := by
  have _ := hfc
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  rw [rightConv_apply]

  set IW : ℝ≥0∞ := ∫⁻ y in W, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) with hIW
  have hIW_top : IW ≠ ⊤ := by
    have h2 := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (two_ne_zero)
      (ENNReal.ofNat_ne_top (n := 2)) hL2.eLpNorm_lt_top
    have hEq : IW = ∫⁻ y in W, ‖φ y‖ₑ ^ (2 : ℝ≥0∞).toReal ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
      rw [hIW, ENNReal.toReal_ofNat]
      refine lintegral_congr fun y => ?_
      rw [ENNReal.rpow_two, enorm_eq_nnnorm]
    rw [hEq]
    exact h2.ne

  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 1)
  have hfB : ∀ x, (‖f x‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal B := fun x => by
    rw [← enorm_eq_nnnorm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hB x)
  have hS : MeasurableSet (tsupport f) := (isClosed_tsupport f).measurableSet
  have hμS_top : adelicGLHaar (Fin 2) (𝓞 K) K (tsupport f) ≠ ⊤ :=
    (hfs.isCompact.measure_lt_top (μ := adelicGLHaar (Fin 2) (𝓞 K) K)).ne

  have h1 : ‖∫ x, φ (g * x) * f x ∂(adelicGLHaar (Fin 2) (𝓞 K) K)‖
      ≤ (∫⁻ x, (‖φ (g * x)‖₊ : ℝ≥0∞) * (‖f x‖₊ : ℝ≥0∞) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)).toReal := by
    refine (norm_integral_le_lintegral_norm _).trans (le_of_eq ?_)
    congr 1
    refine lintegral_congr fun x => ?_
    rw [ofReal_norm, enorm_mul, enorm_eq_nnnorm, enorm_eq_nnnorm]

  have hI : ∫⁻ x, (‖φ (g * x)‖₊ : ℝ≥0∞) * (‖f x‖₊ : ℝ≥0∞) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      ≤ ENNReal.ofReal B * ∫⁻ x in tsupport f, (‖φ (g * x)‖₊ : ℝ≥0∞) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
    calc ∫⁻ x, (‖φ (g * x)‖₊ : ℝ≥0∞) * (‖f x‖₊ : ℝ≥0∞) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
        ≤ ∫⁻ x, (tsupport f).indicator (fun x => ENNReal.ofReal B * (‖φ (g * x)‖₊ : ℝ≥0∞)) x
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
          refine lintegral_mono fun x => ?_
          by_cases hx : x ∈ tsupport f
          · have h2 : (tsupport f).indicator (fun x => ENNReal.ofReal B * (‖φ (g * x)‖₊ : ℝ≥0∞)) x
                = ENNReal.ofReal B * (‖φ (g * x)‖₊ : ℝ≥0∞) := Set.indicator_of_mem hx _
            rw [h2, mul_comm]
            exact mul_le_mul' (hfB x) le_rfl
          · have h0 : f x = 0 := image_eq_zero_of_notMem_tsupport hx
            simp [h0]
      _ = ∫⁻ x in tsupport f, ENNReal.ofReal B * (‖φ (g * x)‖₊ : ℝ≥0∞) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
          lintegral_indicator hS _
      _ = ENNReal.ofReal B * ∫⁻ x in tsupport f, (‖φ (g * x)‖₊ : ℝ≥0∞) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

  have hmeas : AEMeasurable (fun x => (‖φ (g * x)‖₊ : ℝ≥0∞))
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (tsupport f)) :=
    ((hcont.comp (continuous_const.mul continuous_id)).enorm).measurable.aemeasurable
  have hCS : ∫⁻ x in tsupport f, (‖φ (g * x)‖₊ : ℝ≥0∞) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      ≤ (adelicGLHaar (Fin 2) (𝓞 K) K (tsupport f)) ^ (1 / (2 : ℝ)) *
        (∫⁻ x in tsupport f, (‖φ (g * x)‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ^ (1 / (2 : ℝ)) := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (tsupport f))
      Real.HolderConjugate.two_two (f := fun _ => (1 : ℝ≥0∞)) (g := fun x => (‖φ (g * x)‖₊ : ℝ≥0∞))
      aemeasurable_const hmeas
    simp only [Pi.mul_apply, one_mul, ENNReal.rpow_two, one_pow, lintegral_const,
      Measure.restrict_apply_univ] at h
    exact h

  have hJS : ∫⁻ x in tsupport f, (‖φ (g * x)‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      ≤ ENNReal.ofReal |N| * IW := by
    calc ∫⁻ x in tsupport f, (‖φ (g * x)‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
        = ∫⁻ x, (tsupport f).indicator (fun x => (‖φ (g * x)‖₊ : ℝ≥0∞) ^ 2) x
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := (lintegral_indicator hS _).symm
      _ ≤ ∫⁻ x, R.indicator (fun y => (‖φ y‖₊ : ℝ≥0∞) ^ 2) (g * x) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
          refine lintegral_mono fun x => ?_
          by_cases hx : x ∈ tsupport f
          · have hgx : g * x ∈ R := hsub ⟨x, hx, rfl⟩
            have h2 : (tsupport f).indicator (fun x => (‖φ (g * x)‖₊ : ℝ≥0∞) ^ 2) x
                = (‖φ (g * x)‖₊ : ℝ≥0∞) ^ 2 := Set.indicator_of_mem hx _
            have h3 : R.indicator (fun y => (‖φ y‖₊ : ℝ≥0∞) ^ 2) (g * x)
                = (‖φ (g * x)‖₊ : ℝ≥0∞) ^ 2 := Set.indicator_of_mem hgx _
            exact le_of_eq (h2.trans h3.symm)
          · have h2 : (tsupport f).indicator (fun x => (‖φ (g * x)‖₊ : ℝ≥0∞) ^ 2) x = 0 :=
              Set.indicator_of_notMem hx _
            exact h2.trans_le zero_le
      _ = ∫⁻ y, R.indicator (fun y => (‖φ y‖₊ : ℝ≥0∞) ^ 2) y ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
          lintegral_mul_left_eq_self (R.indicator fun y => (‖φ y‖₊ : ℝ≥0∞) ^ 2) g
      _ ≤ ∫⁻ y in R, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
          lintegral_indicator_le (fun y => (‖φ y‖₊ : ℝ≥0∞) ^ 2) R
      _ ≤ ENNReal.ofReal N * IW := hLOW
      _ ≤ ENNReal.ofReal |N| * IW := mul_le_mul' (ENNReal.ofReal_le_ofReal (le_abs_self N)) le_rfl

  have hmain : ∫⁻ x, (‖φ (g * x)‖₊ : ℝ≥0∞) * (‖f x‖₊ : ℝ≥0∞) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      ≤ ENNReal.ofReal B * ((adelicGLHaar (Fin 2) (𝓞 K) K (tsupport f)) ^ (1 / (2 : ℝ)) *
          (ENNReal.ofReal |N| * IW) ^ (1 / (2 : ℝ))) :=
    hI.trans (mul_le_mul' le_rfl (hCS.trans (mul_le_mul' le_rfl
      (ENNReal.rpow_le_rpow hJS (by norm_num)))))
  have hX_top : ENNReal.ofReal B * ((adelicGLHaar (Fin 2) (𝓞 K) K (tsupport f)) ^ (1 / (2 : ℝ)) *
      (ENNReal.ofReal |N| * IW) ^ (1 / (2 : ℝ))) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hμS_top)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hIW_top)))
  have h := ENNReal.toReal_mono hX_top hmain
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hB0, ← ENNReal.toReal_rpow,
    ← ENNReal.toReal_rpow, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg N), ← Real.sqrt_eq_rpow,
    ← Real.sqrt_eq_rpow, ← mul_assoc] at h
  exact h1.trans h

variable (K : Type) [Field K] [NumberField K]

private abbrev μ : Measure (AdelicGL2 (𝓞 K) K) := adelicGLHaar (Fin 2) (𝓞 K) K

variable {K}

private scoped instance instHaarμ : (μ K).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K

variable (K)

private def slab (α β : ℝ) : Set (AdelicGL2 (𝓞 K) K) :=
  {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}

private abbrev Γ : Subgroup (AdelicGL2 (𝓞 K) K) := (globalPoints (𝓞 K) K).range

private def sq (φ : AdelicGL2 (𝓞 K) K → ℂ) (y : AdelicGL2 (𝓞 K) K) : ℝ≥0∞ := (‖φ y‖₊ : ℝ≥0∞) ^ 2

variable {K}

private theorem normDet_mul (x z : AdelicGL2 (𝓞 K) K) :
    ideleNorm K (Matrix.GeneralLinearGroup.det (x * z)) =
      ideleNorm K (Matrix.GeneralLinearGroup.det x) * ideleNorm K (Matrix.GeneralLinearGroup.det z) := by
  rw [map_mul, ideleNorm_mul]

private theorem normDet_central (c : (AdeleRing (𝓞 K) K)ˣ) (x : AdelicGL2 (𝓞 K) K) :
    ideleNorm K (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K c * x)) =
      ideleNorm K c ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det x) := by
  rw [normDet_mul, det_centralScalar, pow_two, ideleNorm_mul, pow_two]

private theorem normDet_global (γ : Matrix.GeneralLinearGroup (Fin 2) K) (x : AdelicGL2 (𝓞 K) K) :
    ideleNorm K (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 K) K γ * x)) =
      ideleNorm K (Matrix.GeneralLinearGroup.det x) := by
  rw [normDet_mul, ideleNorm_det_globalPoints, one_mul]

omit [NumberField K] in

private theorem exists_completion_norm_eq (w : InfinitePlace K) (s : ℝ) (hs : 0 ≤ s) :
    ∃ a : w.Completion, ‖a‖ = s := by
  have hiso := InfinitePlace.Completion.isometry_extensionEmbedding w
  rcases w.isReal_or_isComplex with hw | hw
  · obtain ⟨a, ha⟩ := InfinitePlace.Completion.surjective_extensionEmbeddingOfIsReal hw s
    refine ⟨a, ?_⟩
    have h1 : (InfinitePlace.Completion.extensionEmbedding w a : ℂ) = (s : ℂ) := by
      rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw, ha]
    rw [← hiso.norm_map_of_map_zero (map_zero _) a, h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
  · obtain ⟨a, ha⟩ := InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex hw (s : ℂ)
    refine ⟨a, ?_⟩
    rw [← hiso.norm_map_of_map_zero (map_zero _) a, ha, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]

private theorem exists_ideleNorm_eq (t : ℝ) (ht : 0 < t) : ∃ c : (AdeleRing (𝓞 K) K)ˣ, ideleNorm K c = t := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
  obtain ⟨a, ha⟩ := exists_completion_norm_eq w (t ^ ((w.mult : ℝ)⁻¹)) (Real.rpow_nonneg ht.le _)
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, norm_zero] at ha
    exact (Real.rpow_pos_of_pos ht _).ne ha
  refine ⟨archCentralUnit K w (Units.mk0 a ha0), ?_⟩
  unfold ideleNorm
  rw [AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one K _ (archCentralUnit_snd w _),
    Finset.prod_eq_single w (fun v _ hv => by rw [archCentralUnit_fst_of_ne w _ hv, norm_one, one_pow])
      (fun h => (h (Finset.mem_univ w)).elim),
    archCentralUnit_fst_self]
  show ‖a‖ ^ w.mult = t
  rw [ha, Real.rpow_inv_natCast_pow ht.le InfinitePlace.mult_ne_zero]

private theorem slab_measurable (α β : ℝ) : MeasurableSet (slab K α β) :=
  measurableSet_setOf_ideleNorm_det_mem_Icc K α β

private theorem Γ_smul (γ : Γ K) (x : AdelicGL2 (𝓞 K) K) : γ • x = (γ : AdelicGL2 (𝓞 K) K) * x := rfl

private theorem Γ_smul_eq (γ : Γ K) :
    ∃ γ₀ : Matrix.GeneralLinearGroup (Fin 2) K, (γ : AdelicGL2 (𝓞 K) K) = globalPoints (𝓞 K) K γ₀ := by
  obtain ⟨γ₀, h⟩ := γ.2
  exact ⟨γ₀, h.symm⟩

private theorem slab_Γ_stable (α β : ℝ) (γ : Γ K) (x : AdelicGL2 (𝓞 K) K) :
    γ • x ∈ slab K α β ↔ x ∈ slab K α β := by
  obtain ⟨γ₀, hγ₀⟩ := Γ_smul_eq γ
  show ideleNorm K (Matrix.GeneralLinearGroup.det (_ * x)) ∈ Set.Icc α β ↔ x ∈ slab K α β
  rw [hγ₀, normDet_global]
  exact Iff.rfl

private scoped instance instMeasurableConstSMulΓ : MeasurableConstSMul (Γ K) (AdelicGL2 (𝓞 K) K) :=
  ⟨fun γ => measurable_const_mul (γ : AdelicGL2 (𝓞 K) K)⟩

private theorem smulInvariant_restrict_slab (α β : ℝ) :
    SMulInvariantMeasure (Γ K) (AdelicGL2 (𝓞 K) K) ((μ K).restrict (slab K α β)) := by
  refine ⟨fun γ s hs => ?_⟩
  have hmeas : MeasurableSet ((fun x => γ • x) ⁻¹' s) := (measurable_const_mul (γ : AdelicGL2 (𝓞 K) K)) hs
  rw [Measure.restrict_apply hmeas, Measure.restrict_apply hs]
  have hset : (fun x => γ • x) ⁻¹' s ∩ slab K α β =
      (fun x => (γ : AdelicGL2 (𝓞 K) K) * x) ⁻¹' (s ∩ slab K α β) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    rw [← Γ_smul γ x, slab_Γ_stable]
  rw [hset, measure_preimage_mul]

private theorem countable_K : Countable K :=
  (Module.finBasis ℚ K).equivFun.injective.countable

private theorem countable_Γ : Countable (Γ K) := by
  haveI := countable_K (K := K)
  haveI : Countable (Matrix (Fin 2) (Fin 2) K) := inferInstanceAs (Countable (Fin 2 → Fin 2 → K))
  haveI : Countable (Matrix.GeneralLinearGroup (Fin 2) K) := Units.val_injective.countable
  have h : ((Γ K : Subgroup (AdelicGL2 (𝓞 K) K)) : Set (AdelicGL2 (𝓞 K) K)).Countable := by
    rw [MonoidHom.coe_range]
    exact Set.countable_range _
  exact h.to_subtype

private theorem central_comm (c : (AdeleRing (𝓞 K) K)ˣ) (X : AdelicGL2 (𝓞 K) K) :
    X * centralScalar (𝓞 K) K c = centralScalar (𝓞 K) K c * X :=
  AutomorphicForm.SiegelCovering.mul_centralScalar_comm c X

private theorem measurable_sq (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφ : Continuous φ) : Measurable (sq K φ) :=
  (measurable_coe_nnreal_ennreal.comp hφ.measurable.nnnorm).pow_const 2

private theorem shifts (a b α β : ℝ) (ha : 0 < a) (hβ : 0 < β) (hαβ : α < β) :
    ∃ Zs : Finset (AdeleRing (𝓞 K) K)ˣ, ∀ r ∈ Set.Icc a b, ∃ z ∈ Zs,
      ideleNorm K z ^ 2 * r ∈ Set.Icc α β := by
  classical

  set θ : ℝ := max (α / β) (1 / 2) with hθ
  have hθ_half : (1 / 2 : ℝ) ≤ θ := le_max_right _ _
  have hθ_pos : 0 < θ := by linarith
  have hθ_lt : θ < 1 := max_lt ((div_lt_one hβ).2 hαβ) (by norm_num)
  have hαθ : α ≤ θ * β := by
    have h : α / β ≤ θ := le_max_left _ _
    calc α = α / β * β := (div_mul_cancel₀ α hβ.ne').symm
      _ ≤ θ * β := mul_le_mul_of_nonneg_right h hβ.le

  have hs_pos : ∀ k : ℕ, 0 < θ ^ k * (β / a) := fun k => mul_pos (pow_pos hθ_pos k) (div_pos hβ ha)
  have hz : ∀ k : ℕ, ∃ z : (AdeleRing (𝓞 K) K)ˣ, ideleNorm K z = Real.sqrt (θ ^ k * (β / a)) :=
    fun k => exists_ideleNorm_eq _ (Real.sqrt_pos.2 (hs_pos k))
  choose z hz using hz

  obtain ⟨N, hN⟩ : ∃ N : ℕ, θ ^ N * (b / a) ≤ 1 := by
    rcases le_or_gt b 0 with hb | hb
    · refine ⟨0, ?_⟩
      rw [pow_zero, one_mul]
      exact (div_nonpos_iff.2 (Or.inr ⟨hb, ha.le⟩)).trans zero_le_one
    · obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos ha hb) hθ_lt
      refine ⟨N, ?_⟩
      have h := mul_le_mul_of_nonneg_right hN.le (div_pos hb ha).le
      rwa [div_mul_div_comm, mul_comm b a, div_self (mul_pos ha hb).ne'] at h
  refine ⟨(Finset.range (N + 1)).image z, fun r hr => ?_⟩
  obtain ⟨har, hrb⟩ := hr
  set t : ℝ := r / a with ht
  have ht_one : 1 ≤ t := (one_le_div ha).2 har
  have ht_le : t ≤ b / a := div_le_div_of_nonneg_right hrb ha.le

  have hex : ∃ k : ℕ, θ ^ k * t ≤ 1 :=
    ⟨N, (mul_le_mul_of_nonneg_left ht_le (pow_pos hθ_pos N).le).trans hN⟩
  set k : ℕ := Nat.find hex with hk
  have hk_spec : θ ^ k * t ≤ 1 := Nat.find_spec hex
  have hk_le : k ≤ N := Nat.find_min' hex ((mul_le_mul_of_nonneg_left ht_le (pow_pos hθ_pos N).le).trans hN)
  have hk_lower : θ ≤ θ ^ k * t := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk0, pow_zero, one_mul]
      exact hθ_lt.le.trans ht_one
    · obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, (Nat.succ_pred_eq_of_pos hkpos).symm⟩
      have hjlt : j < k := by omega
      have hmin : ¬ θ ^ j * t ≤ 1 := Nat.find_min hex (hk ▸ hjlt)
      rw [not_le] at hmin
      calc θ = θ * 1 := (mul_one θ).symm
        _ ≤ θ * (θ ^ j * t) := mul_le_mul_of_nonneg_left hmin.le hθ_pos.le
        _ = θ ^ k * t := by rw [hj, pow_succ, mul_comm (θ ^ j) θ, mul_assoc]
  refine ⟨z k, Finset.mem_image_of_mem z (Finset.mem_range.2 (Nat.lt_succ_of_le hk_le)), ?_⟩
  rw [hz k, Real.sq_sqrt (hs_pos k).le]
  have hval : θ ^ k * (β / a) * r = β * (θ ^ k * t) := by
    rw [ht]; ring
  rw [hval]
  constructor
  · calc α ≤ θ * β := hαθ
      _ = β * θ := mul_comm _ _
      _ ≤ β * (θ ^ k * t) := mul_le_mul_of_nonneg_left hk_lower hβ.le
  · calc β * (θ ^ k * t) ≤ β * 1 := mul_le_mul_of_nonneg_left hk_spec hβ.le
      _ = β := mul_one β

private theorem transfer (χ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsLsXiFunction (𝓞 K) K ⊤ χ φ) (z : (AdeleRing (𝓞 K) K)ˣ) (S : Set (AdelicGL2 (𝓞 K) K)) :
    ∫⁻ y in (fun y => centralScalar (𝓞 K) K z * y) ⁻¹' S, sq K φ y ∂(μ K) =
      ENNReal.ofReal ((‖((χ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖⁻¹) ^ 2) * ∫⁻ y in S, sq K φ y ∂(μ K) := by
  have hmp : MeasurePreserving (fun y : AdelicGL2 (𝓞 K) K => centralScalar (𝓞 K) K z * y) (μ K) (μ K) :=
    measurePreserving_mul_left (μ K) _
  have hemb : MeasurableEmbedding (fun y : AdelicGL2 (𝓞 K) K => centralScalar (𝓞 K) K z * y) :=
    (MeasurableEquiv.mulLeft (centralScalar (𝓞 K) K z)).measurableEmbedding
  have hv : (0 : ℝ) < ‖((χ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ := norm_pos_iff.2 (Units.ne_zero _)
  set c : ℝ≥0∞ := (‖((χ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖₊ : ℝ≥0∞) ^ 2 with hc
  have hc0 : c ≠ 0 := pow_ne_zero _ (ENNReal.coe_ne_zero.2 (nnnorm_ne_zero_iff.2 (Units.ne_zero _)))
  have hctop : c ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hpt : ∀ y : AdelicGL2 (𝓞 K) K, sq K φ (centralScalar (𝓞 K) K z * y) = c * sq K φ y := by
    intro y
    simp only [sq, hφ.central_transform ⟨z, Subgroup.mem_top z⟩ y, nnnorm_mul, ENNReal.coe_mul, mul_pow, hc]
  have hconst : ENNReal.ofReal ((‖((χ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖⁻¹) ^ 2) = c⁻¹ := by
    rw [ENNReal.ofReal_pow (inv_nonneg.2 hv.le), ENNReal.ofReal_inv_of_pos hv, ← coe_nnnorm,
      ENNReal.ofReal_coe_nnreal, hc, ENNReal.inv_pow]
  have hS := hmp.setLIntegral_comp_preimage_emb hemb (sq K φ) S
  rw [hconst, ← hS]
  calc ∫⁻ y in (fun y => centralScalar (𝓞 K) K z * y) ⁻¹' S, sq K φ y ∂(μ K)
      = ∫⁻ y in (fun y => centralScalar (𝓞 K) K z * y) ⁻¹' S, c⁻¹ * (c * sq K φ y) ∂(μ K) := by
        refine lintegral_congr fun y => ?_
        rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hctop, one_mul]
    _ = c⁻¹ * ∫⁻ y in (fun y => centralScalar (𝓞 K) K z * y) ⁻¹' S, c * sq K φ y ∂(μ K) :=
        lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hc0)
    _ = c⁻¹ * ∫⁻ y in (fun y => centralScalar (𝓞 K) K z * y) ⁻¹' S, sq K φ (centralScalar (𝓞 K) K z * y)
          ∂(μ K) := by
        simp_rw [hpt]

private theorem unfold (α β : ℝ) (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : IsFundamentalDomain (Γ K) Φ₀ ((μ K).restrict (slab K α β)))
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφc : Continuous φ) (hφΓ : ∀ (γ : Γ K) (y : AdelicGL2 (𝓞 K) K), φ (γ • y) = φ y)
    (E : Set (AdelicGL2 (𝓞 K) K)) (hEm : MeasurableSet E) (hE : E ⊆ slab K α β) (n : ℕ)
    (hn : ∀ y : AdelicGL2 (𝓞 K) K, ({γ : Γ K | y ∈ γ • E} : Set (Γ K)).encard ≤ n) :
    ∫⁻ y in E, sq K φ y ∂(μ K) ≤ (n : ℝ≥0∞) * ∫⁻ y in Φ₀, sq K φ y ∂(μ K) := by
  haveI := countable_Γ (K := K)
  haveI := smulInvariant_restrict_slab (K := K) α β
  have hsqΓ : ∀ (γ : Γ K) (y : AdelicGL2 (𝓞 K) K), sq K φ (γ⁻¹ • y) = sq K φ y := by
    intro γ y
    simp only [sq, hφΓ]

  have hE' : ∫⁻ y in E, sq K φ y ∂(μ K) = ∫⁻ y in E, sq K φ y ∂((μ K).restrict (slab K α β)) := by
    rw [Measure.restrict_restrict' (slab_measurable α β), Set.inter_eq_left.2 hE]
  have hΦ' : ∫⁻ y in Φ₀, sq K φ y ∂((μ K).restrict (slab K α β)) ≤ ∫⁻ y in Φ₀, sq K φ y ∂(μ K) := by
    rw [Measure.restrict_restrict' (slab_measurable α β)]
    exact lintegral_mono_set Set.inter_subset_left
  rw [hE']
  calc ∫⁻ y in E, sq K φ y ∂((μ K).restrict (slab K α β))
      = ∑' γ : Γ K, ∫⁻ y in γ • E ∩ Φ₀, sq K φ (γ⁻¹ • y) ∂((μ K).restrict (slab K α β)) :=
        hΦ₀.setLIntegral_eq_tsum' _ E
    _ = ∑' γ : Γ K, ∫⁻ y in Φ₀, (γ • E).indicator (fun _ => (1 : ℝ≥0∞)) y * sq K φ y
          ∂((μ K).restrict (slab K α β)) := by
        refine tsum_congr fun γ => ?_
        simp_rw [hsqΓ]
        rw [← Measure.restrict_restrict (hEm.const_smul γ), ← lintegral_indicator (hEm.const_smul γ)]
        refine lintegral_congr fun y => ?_
        by_cases hy : y ∈ γ • E <;> simp [Set.indicator, hy]
    _ = ∫⁻ y in Φ₀, (∑' γ : Γ K, (γ • E).indicator (fun _ => (1 : ℝ≥0∞)) y) * sq K φ y
          ∂((μ K).restrict (slab K α β)) := by
        rw [← lintegral_tsum]
        · simp_rw [ENNReal.tsum_mul_right]
        · intro γ
          exact ((measurable_const.indicator (hEm.const_smul γ)).mul (measurable_sq φ hφc)).aemeasurable
    _ ≤ ∫⁻ y in Φ₀, (n : ℝ≥0∞) * sq K φ y ∂((μ K).restrict (slab K α β)) := by
        refine lintegral_mono fun y => ?_
        gcongr
        have h1 : ∑' γ : ({γ : Γ K | y ∈ γ • E} : Set (Γ K)), (1 : ℝ≥0∞) =
            ∑' γ : Γ K, (γ • E).indicator (fun _ => (1 : ℝ≥0∞)) y :=
          (tsum_subtype ({γ : Γ K | y ∈ γ • E} : Set (Γ K)) fun _ => (1 : ℝ≥0∞)).trans
            (tsum_congr fun γ => by by_cases hγ : y ∈ γ • E <;> simp [Set.indicator, hγ])
        rw [← h1, ENNReal.tsum_set_one]
        calc (({γ : Γ K | y ∈ γ • E} : Set (Γ K)).encard : ℝ≥0∞)
            ≤ ((n : ℕ∞) : ℝ≥0∞) := ENat.toENNReal_le.2 (hn y)
          _ = (n : ℝ≥0∞) := ENat.toENNReal_coe n
    _ = (n : ℝ≥0∞) * ∫⁻ y in Φ₀, sq K φ y ∂((μ K).restrict (slab K α β)) := lintegral_const_mul _ (measurable_sq φ hφc)
    _ ≤ (n : ℝ≥0∞) * ∫⁻ y in Φ₀, sq K φ y ∂(μ K) := by gcongr

private theorem globalPoints_entry (δ : Matrix.GeneralLinearGroup (Fin 2) K) (i j : Fin 2) :
    ((globalPoints (𝓞 K) K δ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j
      = algebraMap K (AdeleRing (𝓞 K) K) ((δ : Matrix (Fin 2) (Fin 2) K) i j) := rfl

private theorem finite_setOf_mem_of_isCompact {E : Set (AdelicGL2 (𝓞 K) K)} (hE : IsCompact E) :
    ({γ : Γ K | (γ : AdelicGL2 (𝓞 K) K) ∈ E} : Set (Γ K)).Finite := by

  have hfin : ∀ i j : Fin 2, ({q : K | algebraMap K (AdeleRing (𝓞 K) K) q ∈
      (fun g : AdelicGL2 (𝓞 K) K => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j) '' E} : Set K).Finite :=
    fun i j =>
      NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact K
        (hE.image (Units.continuous_val.matrix_elem i j))

  have hT : (Set.pi Set.univ fun i : Fin 2 => Set.pi Set.univ fun j : Fin 2 =>
      algebraMap K (AdeleRing (𝓞 K) K) '' {q : K | algebraMap K (AdeleRing (𝓞 K) K) q ∈
        (fun g : AdelicGL2 (𝓞 K) K => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j) '' E} :
          Set (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).Finite :=
    Set.Finite.pi fun i => Set.Finite.pi fun j => (hfin i j).image _
  refine Set.Finite.of_finite_image (f := fun γ : Γ K =>
    ((γ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))) (hT.subset ?_) ?_
  · rintro _ ⟨γ, hγ, rfl⟩
    obtain ⟨δ, hδ⟩ := Γ_smul_eq γ
    intro i _ j _
    refine ⟨(δ : Matrix (Fin 2) (Fin 2) K) i j, ⟨(γ : AdelicGL2 (𝓞 K) K), hγ, ?_⟩, ?_⟩
    · show ((γ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j = _
      rw [hδ, globalPoints_entry]
    · show _ = ((γ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j
      rw [hδ, globalPoints_entry]
  · intro γ _ γ' _ h
    exact Subtype.ext (Units.ext h)

private theorem exists_forall_encard_le_of_isCompact {E : Set (AdelicGL2 (𝓞 K) K)} (hE : IsCompact E) :
    ∃ n : ℕ, ∀ y : AdelicGL2 (𝓞 K) K, ({γ : Γ K | y ∈ γ • E} : Set (Γ K)).encard ≤ n := by
  have hEE : IsCompact (Set.image2 (fun e e' : AdelicGL2 (𝓞 K) K => e * e'⁻¹) E E) := by
    rw [← Set.image_prod]
    exact (hE.prod hE).image (continuous_fst.mul continuous_snd.inv)
  have hS := finite_setOf_mem_of_isCompact hEE
  refine ⟨hS.toFinset.card, fun y => ?_⟩
  rcases ({γ : Γ K | y ∈ γ • E} : Set (Γ K)).eq_empty_or_nonempty with h | ⟨γ₀, hγ₀⟩
  · rw [h, Set.encard_empty]
    exact zero_le
  obtain ⟨e₀, he₀, hγ₀e₀⟩ := hγ₀
  beta_reduce at hγ₀e₀
  rw [Γ_smul] at hγ₀e₀
  calc ({γ : Γ K | y ∈ γ • E} : Set (Γ K)).encard
      = ((fun γ : Γ K => γ₀⁻¹ * γ) '' {γ : Γ K | y ∈ γ • E}).encard :=
        (Set.InjOn.encard_image fun _ _ _ _ h => mul_left_cancel h).symm
    _ ≤ ({γ : Γ K | (γ : AdelicGL2 (𝓞 K) K) ∈
          Set.image2 (fun e e' : AdelicGL2 (𝓞 K) K => e * e'⁻¹) E E} : Set (Γ K)).encard := by
        refine Set.encard_le_encard ?_
        rintro _ ⟨γ, hγ, rfl⟩
        obtain ⟨e, he, hγe⟩ := hγ
        beta_reduce at hγe
        rw [Γ_smul] at hγe
        have h : (γ₀ : AdelicGL2 (𝓞 K) K) * e₀ = (γ : AdelicGL2 (𝓞 K) K) * e := hγ₀e₀.trans hγe.symm
        refine ⟨e₀, he₀, e, he, ?_⟩
        show e₀ * e⁻¹ = ((γ₀⁻¹ * γ : Γ K) : AdelicGL2 (𝓞 K) K)
        rw [Subgroup.coe_mul, Subgroup.coe_inv]
        calc e₀ * e⁻¹ = (γ₀ : AdelicGL2 (𝓞 K) K)⁻¹ * ((γ₀ : AdelicGL2 (𝓞 K) K) * e₀) * e⁻¹ := by group
          _ = (γ₀ : AdelicGL2 (𝓞 K) K)⁻¹ * ((γ : AdelicGL2 (𝓞 K) K) * e) * e⁻¹ := by rw [h]
          _ = (γ₀ : AdelicGL2 (𝓞 K) K)⁻¹ * (γ : AdelicGL2 (𝓞 K) K) := by group
    _ = hS.toFinset.card := hS.encard_eq_coe_toFinset_card

private theorem detRange_of_isCompact {E : Set (AdelicGL2 (𝓞 K) K)} (hE : IsCompact E) :
    ∃ a b : ℝ, 0 < a ∧ ∀ y ∈ E, ideleNorm K (Matrix.GeneralLinearGroup.det y) ∈ Set.Icc a b := by
  rcases E.eq_empty_or_nonempty with hEe | hEne
  · exact ⟨1, 1, one_pos, fun y hy => (by rw [hEe] at hy; exact hy.elim)⟩
  obtain ⟨ymin, -, hmin⟩ := hE.exists_isMinOn hEne (continuous_ideleNorm_det K).continuousOn
  obtain ⟨ymax, -, hmax⟩ := hE.exists_isMaxOn hEne (continuous_ideleNorm_det K).continuousOn
  exact ⟨_, _, ideleNorm_pos (Matrix.GeneralLinearGroup.det ymin), fun y hy => ⟨hmin hy, hmax hy⟩⟩

private theorem compact_mass_bound (χ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (α β : ℝ) (hβ : 0 < β)
    (hαβ : α < β) (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : IsFundamentalDomain (Γ K) Φ₀ ((μ K).restrict (slab K α β)))
    {E : Set (AdelicGL2 (𝓞 K) K)} (hE : IsCompact E) :
    ∃ N : ℝ, ∀ φ : AdelicGL2 (𝓞 K) K → ℂ, IsLsXiFunction (𝓞 K) K ⊤ χ φ → Continuous φ →
      ∫⁻ y in E, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
        ≤ ENNReal.ofReal N * ∫⁻ y in Φ₀, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  obtain ⟨a, b, ha, hab⟩ := detRange_of_isCompact hE
  obtain ⟨Zs, hZs⟩ := shifts (K := K) a b α β ha hβ hαβ
  obtain ⟨n, hn⟩ := exists_forall_encard_le_of_isCompact hE
  set w : (AdeleRing (𝓞 K) K)ˣ → ℝ := fun z => (‖((χ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖⁻¹) ^ 2 with hw
  have hw_nonneg : ∀ z, 0 ≤ w z := fun z => sq_nonneg _
  refine ⟨(∑ z ∈ Zs, w z) * n, fun φ hφ hφc => ?_⟩
  have hφΓ : ∀ (γ : Γ K) (y : AdelicGL2 (𝓞 K) K), φ (γ • y) = φ y := by
    intro γ y
    obtain ⟨γ₀, hγ₀⟩ := Γ_smul_eq γ
    rw [Γ_smul, hγ₀, hφ.left_invariant]

  set piece : (AdeleRing (𝓞 K) K)ˣ → Set (AdelicGL2 (𝓞 K) K) := fun z =>
    E ∩ {y | ideleNorm K z ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det y) ∈ Set.Icc α β} with hpiece
  have hpiece_meas : ∀ z, MeasurableSet (piece z) := fun z =>
    hE.isClosed.measurableSet.inter
      (measurableSet_Icc.preimage ((continuous_ideleNorm_det K).const_mul _).measurable)
  have hcover : E ⊆ ⋃ z : Zs, piece z := by
    intro y hy
    obtain ⟨z, hz, hzr⟩ := hZs _ (hab y hy)
    exact Set.mem_iUnion.2 ⟨⟨z, hz⟩, hy, hzr⟩

  set shifted : (AdeleRing (𝓞 K) K)ˣ → Set (AdelicGL2 (𝓞 K) K) := fun z =>
    (fun y => centralScalar (𝓞 K) K z * y) '' piece z with hshifted
  have hshifted_meas : ∀ z, MeasurableSet (shifted z) := fun z =>
    (MeasurableEquiv.mulLeft (centralScalar (𝓞 K) K z)).measurableSet_image.2 (hpiece_meas z)
  have hshifted_slab : ∀ z, shifted z ⊆ slab K α β := by
    rintro z _ ⟨y, ⟨-, hy⟩, rfl⟩
    show ideleNorm K (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z * y)) ∈ Set.Icc α β
    rw [normDet_central]
    exact hy
  have hshifted_count : ∀ z y, ({γ : Γ K | y ∈ γ • shifted z} : Set (Γ K)).encard ≤ n := by
    intro z y
    refine (Set.encard_le_encard ?_).trans (hn ((centralScalar (𝓞 K) K z)⁻¹ * y))
    rintro γ ⟨y₀, ⟨y₁, ⟨hy₁, -⟩, rfl⟩, rfl⟩
    refine ⟨y₁, hy₁, ?_⟩
    beta_reduce
    rw [Γ_smul, Γ_smul, ← mul_assoc (γ : AdelicGL2 (𝓞 K) K), central_comm, mul_assoc, inv_mul_cancel_left]

  have hpiece_bound : ∀ z, ∫⁻ y in piece z, sq K φ y ∂(μ K) ≤
      ENNReal.ofReal (w z) * ((n : ℝ≥0∞) * ∫⁻ y in Φ₀, sq K φ y ∂(μ K)) := by
    intro z
    calc ∫⁻ y in piece z, sq K φ y ∂(μ K)
        ≤ ∫⁻ y in (fun y => centralScalar (𝓞 K) K z * y) ⁻¹' shifted z, sq K φ y ∂(μ K) :=
          lintegral_mono_set (Set.subset_preimage_image _ _)
      _ = ENNReal.ofReal (w z) * ∫⁻ y in shifted z, sq K φ y ∂(μ K) := transfer χ φ hφ z _
      _ ≤ ENNReal.ofReal (w z) * ((n : ℝ≥0∞) * ∫⁻ y in Φ₀, sq K φ y ∂(μ K)) := by
          gcongr
          exact unfold α β Φ₀ hΦ₀ φ hφc hφΓ (shifted z) (hshifted_meas z) (hshifted_slab z) n (hshifted_count z)

  show ∫⁻ y in E, sq K φ y ∂(μ K) ≤ ENNReal.ofReal ((∑ z ∈ Zs, w z) * n) * ∫⁻ y in Φ₀, sq K φ y ∂(μ K)
  calc ∫⁻ y in E, sq K φ y ∂(μ K)
      ≤ ∫⁻ y in ⋃ z : Zs, piece z, sq K φ y ∂(μ K) := lintegral_mono_set hcover
    _ ≤ ∑' z : Zs, ∫⁻ y in piece z, sq K φ y ∂(μ K) := lintegral_iUnion_le _ _
    _ = ∑ z : Zs, ∫⁻ y in piece z, sq K φ y ∂(μ K) := tsum_fintype _
    _ ≤ ∑ z : Zs, ENNReal.ofReal (w z) * ((n : ℝ≥0∞) * ∫⁻ y in Φ₀, sq K φ y ∂(μ K)) :=
        Finset.sum_le_sum fun z _ => hpiece_bound z
    _ = (∑ z : Zs, ENNReal.ofReal (w z)) * (n : ℝ≥0∞) * ∫⁻ y in Φ₀, sq K φ y ∂(μ K) := by
        rw [← Finset.sum_mul, mul_assoc]
    _ = ENNReal.ofReal ((∑ z ∈ Zs, w z) * n) * ∫⁻ y in Φ₀, sq K φ y ∂(μ K) := by
        rw [← Finset.sum_coe_sort Zs w, ENNReal.ofReal_mul (Finset.sum_nonneg fun (z : Zs) _ => hw_nonneg z),
          ENNReal.ofReal_sum_of_nonneg fun (z : Zs) _ => hw_nonneg z, ENNReal.ofReal_natCast]

private theorem per_translate
    (F : Type) [Field F] [NumberField F]
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (c u d₁ d₂ : ℝ) (hc : 0 < c) (hd₁ : 0 < d₁)
    (α β : ℝ) (hβ : 0 < β) (hαβ : α < β)
    (Φ₀ : Set (AdelicGL2 (𝓞 F) F))
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
        {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (x : AdelicGL2 (𝓞 F) F) :
    ∃ Cx : ℝ, 0 ≤ Cx ∧ ∀ φ : AdelicGL2 (𝓞 F) F → ℂ,
      IsLsXiFunction (𝓞 F) F ⊤ ξ φ →
        IsCuspidalFn ((adelicAddHaar (𝓞 F) F)[|adelicBox F]) unipotentGL2 φ →
          Continuous φ →
            MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀) →
              ∀ s ∈ centreCutSiegelSet F c u d₁ d₂,
                ‖rightConv F φ f (s * x)‖ ≤
                  Cx * (eLpNorm φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀)).toReal := by
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F

  obtain ⟨hf_cont, hf_supp⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hf
  obtain ⟨B, hB⟩ := hf_cont.bounded_above_of_compact_support hf_supp
  have hB' : ∀ y, ‖f y‖ ≤ |B| := fun y => (hB y).trans (le_abs_self B)
  have hft : IsFactorizableTestFn F (fun y => f (x⁻¹ * y)) :=
    isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn F f hf x
  obtain ⟨hft_cont, hft_supp⟩ :=
    continuous_and_hasCompactSupport_of_isFactorizableTestFn F (fun y => f (x⁻¹ * y)) hft

  obtain ⟨T₁, A, M, hL1⟩ :=
   exists_forall_setLIntegral_nnnorm_sq_le_mul_archHeight_pow_mul_setLIntegral_of_isLsXiFunction_of_isFundamentalDomain
     F ξ hft_supp.isCompact c u d₁ d₂ hc hd₁ α β hβ hαβ Φ₀ hΦ₀
  obtain ⟨CN, hP1⟩ :=
    norm_tsum_sub_average_le_mul_inv_archHeight_pow_of_isFactorizableTestFn
      F (fun y => f (x⁻¹ * y)) hft 0 u A
  obtain ⟨Ccap, hH0⟩ := h0_bound F c u d₁ d₂ hc (max T₁ 1)
  obtain ⟨M₀, hM₀, hμR⟩ := r1_bound F c u d₁ d₂ hc hft_supp.isCompact

  obtain ⟨Kcap, hKcap, hK⟩ : ∃ Kc : Set (AdelicGL2 (𝓞 F) F),
      Kc = centreCutSiegelSet F c u d₁ d₂ ∩
        {g | ∀ w : InfinitePlace F, localHeight (archComponent F w (glArch (𝓞 F) F g)) ≤ Ccap} ∧
      IsCompact Kc :=
    ⟨_, rfl, isCompact_centreCutSiegelSet_inter_heightCap F hc hd₁⟩
  have hRc : IsCompact (Set.image2 (fun (s : AdelicGL2 (𝓞 F) F) (k : AdelicGL2 (𝓞 F) F) => s * x * k)
      Kcap (tsupport f)) := by
    rw [← Set.image_prod]
    exact (hK.prod hf_supp.isCompact).image ((continuous_fst.mul continuous_const).mul continuous_snd)
  obtain ⟨N, hN⟩ := compact_mass_bound ξ α β hβ hαβ Φ₀ hΦ₀ hRc

  refine ⟨|CN| * Real.sqrt M₀ * Real.sqrt |M| +
      |B| * Real.sqrt ((adelicGLHaar (Fin 2) (𝓞 F) F (tsupport f)).toReal) * Real.sqrt |N|,
    by positivity, fun φ hls hφc hcont hL2 s hs => ?_⟩
  have hseam := seam_bound F φ Φ₀
  by_cases hw : ∃ w : InfinitePlace F, Ccap < localHeight (archComponent F w (glArch (𝓞 F) F s))
  ·

    have hφN : ∀ (β : F) (y : GL (Fin 2) (AdeleRing (𝓞 F) F)),
        φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * y) = φ y := by
      intro β y
      have h := hls.left_invariant (unipotentGL2 β) y
      rwa [globalPoints_unipotentGL2] at h

    have hφi : LocallyIntegrable φ (adelicGLHaar (Fin 2) (𝓞 F) F) := hcont.locallyIntegrable

    have hH : max T₁ 1 < archHeight F (glArch (𝓞 F) F s) := hH0 s hs hw
    have hT₁ : T₁ < archHeight F (glArch (𝓞 F) F s) := lt_of_le_of_lt (le_max_left _ _) hH
    have h1 : 1 ≤ archHeight F (glArch (𝓞 F) F s) := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hH)

    have hs' := mem_centreCutSiegelSet_iff.mp hs
    have hs_int : s ∈ integralWindowedSiegelSet F 0 u := by
      simp only [integralWindowedSiegelSet, Set.mem_setOf_eq]
      exact ⟨hs'.1, le_of_lt (archHeight_pos F _), hs'.2.2.1⟩

    have hPy := hP1 s hs_int h1
    have hU := norm_integral_mul_le_mul_setIntegral_norm_of_isCuspidalFn F φ (fun y => f (x⁻¹ * y)) s
      hφN hφi hφc hft_cont hft_supp (CN * (archHeight F (glArch (𝓞 F) F s))⁻¹ ^ A) hPy

    rw [rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply F φ f s x]
    have hsub : rightConv F φ (fun y => f (x⁻¹ * y)) s
        = ∫ y, φ y * (fun y => f (x⁻¹ * y)) (s⁻¹ * y) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
      rw [rightConv_apply]
      have h := integral_mul_left_eq_self (μ := adelicGLHaar (Fin 2) (𝓞 F) F)
        (fun y => φ y * (fun y => f (x⁻¹ * y)) (s⁻¹ * y)) s
      simp only [inv_mul_cancel_left] at h
      exact h
    rw [hsub]

    have hcs := cs_bound F φ (fun y => f (x⁻¹ * y)) s Φ₀ _ CN M M₀ _ A hM₀ h1 hcont hL2
      hU (hL1 φ hls hcont s hs hT₁) (hμR s hs)
    refine hcs.trans ?_
    rw [Real.sqrt_mul (abs_nonneg M), hseam, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) ENNReal.toReal_nonneg
  ·
    have hcap : ∀ w : InfinitePlace F, localHeight (archComponent F w (glArch (𝓞 F) F s)) ≤ Ccap :=
      fun w => le_of_not_gt fun h => hw ⟨w, h⟩
    have hsK : s ∈ Kcap := by
      rw [hKcap]
      exact ⟨hs, hcap⟩
    have hsub : (fun y => s * x * y) '' tsupport f
        ⊆ Set.image2 (fun (s : AdelicGL2 (𝓞 F) F) (k : AdelicGL2 (𝓞 F) F) => s * x * k) Kcap (tsupport f) := by
      rintro _ ⟨k, hk, rfl⟩
      exact ⟨s, hsK, k, hk, rfl⟩
    have hlow := lowcs_bound F φ f (s * x) _ Φ₀ |B| N hB' hf_cont hf_supp hcont hL2 hsub (hN φ hls hcont)
    refine hlow.trans ?_
    rw [Real.sqrt_mul (abs_nonneg N), hseam, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) ENNReal.toReal_nonneg

private theorem core
    (F : Type) [Field F] [NumberField F]
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) (hc : 0 < c) (hd₁ : 0 < d₁)
    (α β : ℝ) (hβ : 0 < β) (hαβ : α < β)
    (Φ₀ : Set (AdelicGL2 (𝓞 F) F))
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
        {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
    ∃ C : ℝ, ∀ φ : AdelicGL2 (𝓞 F) F → ℂ,
      IsLsXiFunction (𝓞 F) F ⊤ ξ φ →
        IsCuspidalFn ((adelicAddHaar (𝓞 F) F)[|adelicBox F]) unipotentGL2 φ →
          Continuous φ →
            MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀) →
              ∀ g ∈ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂),
                ‖rightConv F φ f g‖ ≤
                  C * (eLpNorm φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀)).toReal := by
  classical
  have hper := per_translate F ξ f hf c u d₁ d₂ hc hd₁ α β hβ hαβ Φ₀ hΦ₀
  choose Cx hCx0 hCx using hper
  refine ⟨∑ y ∈ T, Cx y, fun φ hls hφc hcont hL2 g hg => ?_⟩
  obtain ⟨x, hxT, hgx⟩ := Set.mem_iUnion₂.mp hg
  obtain ⟨s, hs, rfl⟩ := hgx
  exact (hCx x φ hls hφc hcont hL2 s hs).trans
    (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun y _ => hCx0 y) hxT) ENNReal.toReal_nonneg)

end UniformSupOverFundamentalDomain
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCuspidalFn_of_isFundamentalDomain.UniformSupOverFundamentalDomain"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCuspidalFn_of_isFundamentalDomain.UniformSupOverFundamentalDomain"

theorem solution
    (K : Type) [Field K] [NumberField K]
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : IsFactorizableTestFn K f)
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (hc : 0 < c) (hd₁ : 0 < d₁)
    (α β : ℝ) (hβ : 0 < β) (hαβ : α < β)
    (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
    ∃ C : ℝ, ∀ φ : AdelicGL2 (𝓞 K) K → ℂ,
      IsLsXiFunction (𝓞 K) K ⊤ ξ φ →
        IsCuspidalFn ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) unipotentGL2 φ →
          Continuous φ →
            MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀) →
              ∀ g ∈ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂),
                ‖rightConv K φ f g‖ ≤
                  C * (eLpNorm φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀)).toReal :=
  UniformSupOverFundamentalDomain.core K ξ f hf c u d₁ d₂ T hc hd₁ α β hβ hαβ Φ₀ hΦ₀

end S_AutomorphicForm_exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCuspidalFn_of_isFundamentalDomain
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCuspidalFn_of_isFundamentalDomain (solution)
