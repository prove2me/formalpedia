-- Prove2me | solution 1 for AutomorphicForm.CuspidalSpectrum.exists_norm_toCarrier_rightConv_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/775d37de-1522-509d-995f-9f51f7519eae

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Theorems.Thm_AutomorphicForm_adjoint_rightConv_weightedPairing_of_isLsXiFunction
import Theorems.Thm_AutomorphicForm_rightTranslate_adjoint_weightedPairing_of_isLsXiFunction
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_norm_toCarrier_rightConv_le
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

theorem solution
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (g : AdelicGL2 (𝓞 F) F → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ contMemberSubmodule F Φ₀ ξ),
        ∃ hφg : rightConv F φ g ∈ memberSubmodule F Φ₀ ξ,
          ‖toCarrier F hΦ₀ σ ξ ⟨rightConv F φ g, hφg⟩‖ ≤ C * ‖toCarrier F hΦ₀ σ ξ ⟨φ, hφ.1⟩‖ := by
  classical
  haveI hBorel : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI hHaar := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI hSC : SecondCountableTopology (AdelicGL2 (𝓞 F) F) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  set μ : Measure (AdelicGL2 (𝓞 F) F) := adelicGLHaar (Fin 2) (𝓞 F) F with hμ

  set Wr : AdelicGL2 (𝓞 F) F → ℝ := fun x => NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) with hWr
  have hw_cont : Continuous fun y : AdelicGL2 (𝓞 F) F => NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) :=
    NumberField.TateGlobal.continuous_ideleNorm_det F
  have hrpow : ∀ p : ℝ, Continuous fun y : AdelicGL2 (𝓞 F) F =>
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ p :=
    fun p => hw_cont.rpow_const fun y => Or.inl (NumberField.TateGlobal.ideleNorm_pos _).ne'
  have hWr_cont : Continuous Wr := hrpow (-σ)
  have hWr_nonneg : ∀ x, 0 ≤ Wr x := fun x => Real.rpow_nonneg (NumberField.TateGlobal.ideleNorm_pos _).le _

  have hres : μ.restrict Φ₀ = (μ.restrict (detNormSlab F α β)).restrict Φ₀ := by
    rw [Measure.restrict_restrict₀ hΦ₀.isFundamentalDomain.nullMeasurableSet, Set.inter_eq_left.mpr hΦ₀.subset]
  have hae : ∀ᵐ x ∂(μ.restrict Φ₀), x ∈ Φ₀ := by
    rw [hres]; exact ae_restrict_mem₀ hΦ₀.isFundamentalDomain.nullMeasurableSet
  set M : ℝ := max (α ^ (-σ)) (β ^ (-σ)) with hM
  have hbound : ∀ x ∈ Φ₀, Wr x ≤ M := by
    intro x hx
    obtain ⟨h1, h2⟩ := hΦ₀.subset hx
    rcases le_or_gt 0 (-σ) with hs | hs
    · exact (Real.rpow_le_rpow (hΦ₀.pos.le.trans h1) h2 hs).trans (le_max_right _ _)
    · exact (Real.rpow_le_rpow_of_nonpos hΦ₀.pos h1 hs.le).trans (le_max_left _ _)

  have hQint : ∀ ψ : AdelicGL2 (𝓞 F) F → ℂ, MemLp ψ 2 (μ.restrict Φ₀) →
      Integrable (fun x => ‖ψ x‖ ^ 2 * Wr x) (μ.restrict Φ₀) := by
    intro ψ hψ
    have h2 : Integrable (fun x => ‖ψ x‖ ^ 2) (μ.restrict Φ₀) := (memLp_two_iff_integrable_sq_norm hψ.1).mp hψ
    refine h2.mul_bdd hWr_cont.aestronglyMeasurable (c := M) ?_
    filter_upwards [hae] with x hx
    rw [Real.norm_of_nonneg (hWr_nonneg x)]
    exact hbound x hx

  set N1 : ℝ := ∫ y, ‖g y‖ ∂μ with hN1
  set N2 : ℝ := ∫ y, ‖g y‖ * NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ σ ∂μ with hN2
  have hN1_nonneg : 0 ≤ N1 := integral_nonneg fun _ => norm_nonneg _
  have hN2_nonneg : 0 ≤ N2 := integral_nonneg fun y =>
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (NumberField.TateGlobal.ideleNorm_pos _).le _)
  have hg1_int : Integrable (fun y => ‖g y‖) μ := (hg.norm).integrable_of_hasCompactSupport hgc.norm
  have hg2_int : Integrable (fun y => ‖g y‖ * NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ σ) μ :=
    ((hg.norm).mul (hrpow σ)).integrable_of_hasCompactSupport hgc.norm.mul_right
  refine ⟨Real.sqrt (N1 * N2), Real.sqrt_nonneg _, fun φ hφ => ?_⟩

  obtain ⟨hφlx, hφ2⟩ := (mem_memberSubmodule_iff' F Φ₀ ξ φ).mp hφ.1
  have hφc : Continuous φ := hφ.2
  have hA := AutomorphicForm.adjoint_rightConv_weightedPairing_of_isLsXiFunction F α β hΦ₀.pos Φ₀ hΦ₀.subset
    hΦ₀.isFundamentalDomain ξ σ hσ φ φ hφlx hφlx hφc hφc hφ2 hφ2 g hg hgc
  have hlsxi : IsLsXiFunction (𝓞 F) F ⊤ ξ (rightConv F φ g) := by
    refine ⟨fun γ x => ?_, fun z x => ?_⟩
    · rw [← rightConv_comp_mul_left]
      simp_rw [hφlx.left_invariant γ]
    · rw [← rightConv_comp_mul_left]
      simp_rw [hφlx.central_transform z]
      simp only [rightConv_apply, mul_assoc]
      exact integral_const_mul _ _
  have hφg : rightConv F φ g ∈ memberSubmodule F Φ₀ ξ := (mem_memberSubmodule_iff' F Φ₀ ξ _).mpr ⟨hlsxi, hA.1⟩
  refine ⟨hφg, ?_⟩

  have normsq : ∀ (ψ : AdelicGL2 (𝓞 F) F → ℂ) (hψ : ψ ∈ memberSubmodule F Φ₀ ξ),
      ‖toCarrier F hΦ₀ σ ξ ⟨ψ, hψ⟩‖ ^ 2 = ∫ x in Φ₀, ‖ψ x‖ ^ 2 * Wr x ∂μ := by
    intro ψ hψ
    rw [← @inner_self_eq_norm_sq ℂ, MeasureTheory.L2.inner_def]
    have hae_a : (toCarrier F hΦ₀ σ ξ ⟨ψ, hψ⟩ : AdelicGL2 (𝓞 F) F → ℂ) =ᵐ[weightedMeasure F Φ₀ σ] ψ :=
      MemLp.coeFn_toLp (memLp_weightedMeasure_of_mem F hΦ₀ σ hψ)
    have h1 : ∫ x, ⟪(toCarrier F hΦ₀ σ ξ ⟨ψ, hψ⟩ : AdelicGL2 (𝓞 F) F → ℂ) x, (toCarrier F hΦ₀ σ ξ ⟨ψ, hψ⟩ : AdelicGL2 (𝓞 F) F → ℂ) x⟫_ℂ
          ∂(weightedMeasure F Φ₀ σ) = ∫ x, ((‖ψ x‖ ^ 2 : ℝ) : ℂ) ∂(weightedMeasure F Φ₀ σ) := by
      apply integral_congr_ae
      filter_upwards [hae_a] with x hxa
      rw [hxa, RCLike.inner_apply, RCLike.mul_conj]
      norm_cast
    rw [h1]
    unfold weightedMeasure
    rw [integral_withDensity_eq_integral_toReal_smul]
    · rw [← integral_re]
      · refine integral_congr_ae (ae_of_all _ fun x => ?_)
        show RCLike.re ((ENNReal.ofReal (weight F σ x)).toReal • ((‖ψ x‖ ^ 2 : ℝ) : ℂ)) = ‖ψ x‖ ^ 2 * Wr x
        rw [weight_def, ENNReal.toReal_ofReal (hWr_nonneg x), Complex.real_smul, ← Complex.ofReal_mul,
          RCLike.re_to_complex, Complex.ofReal_re, mul_comm]
      ·
        have hψ2 := ((isAutomorphicFnAt_fdPins_iff F Φ₀ ξ ψ).mp hψ).2
        have := (hQint ψ hψ2).ofReal (𝕜 := ℂ)
        refine (this.congr (ae_of_all _ fun x => ?_))
        show ((‖ψ x‖ ^ 2 * Wr x : ℝ) : ℂ) = (ENNReal.ofReal (weight F σ x)).toReal • ((‖ψ x‖ ^ 2 : ℝ) : ℂ)
        rw [weight_def, ENNReal.toReal_ofReal (hWr_nonneg x), Complex.real_smul]
        push_cast
        ring
    · exact (hWr_cont.measurable).ennreal_ofReal
    · exact ae_of_all _ fun x => ENNReal.ofReal_lt_top

  have htrans : ∀ y : AdelicGL2 (𝓞 F) F, MemLp (fun x => φ (x * y)) 2 (μ.restrict Φ₀) ∧
      ∫ x in Φ₀, ‖φ (x * y)‖ ^ 2 * Wr x ∂μ =
        NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ σ * ∫ x in Φ₀, ‖φ x‖ ^ 2 * Wr x ∂μ := by
    intro y
    have hT1 := AutomorphicForm.rightTranslate_adjoint_weightedPairing_of_isLsXiFunction F α β hΦ₀.pos Φ₀ hΦ₀.subset
      hΦ₀.isFundamentalDomain ξ σ hσ φ φ hφlx hφlx hφc hφc hφ2 hφ2 y
    have hv_lx : IsLsXiFunction (𝓞 F) F ⊤ ξ (fun x => φ (x * y)) :=
      ⟨fun γ x => by simp only [mul_assoc]; exact hφlx.left_invariant γ (x * y),
       fun z x => by simp only [mul_assoc]; exact hφlx.central_transform z (x * y)⟩
    have hvc : Continuous (fun x => φ (x * y)) := hφc.comp (continuous_id.mul continuous_const)
    have hT2 := AutomorphicForm.rightTranslate_adjoint_weightedPairing_of_isLsXiFunction F α β hΦ₀.pos Φ₀ hΦ₀.subset
      hΦ₀.isFundamentalDomain ξ σ hσ φ (fun x => φ (x * y)) hφlx hv_lx hφc hvc hφ2 hT1.1 y
    refine ⟨hT1.1, ?_⟩
    have h3 := hT2.2.2
    simp only [inv_mul_cancel_right, RCLike.mul_conj] at h3
    rw [← hμ] at h3
    have h3' : ∫ x in Φ₀, ((‖φ (x * y)‖ : ℝ) : ℂ) ^ 2 * ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ) ∂μ =
        ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ σ : ℝ) : ℂ) *
          ∫ x in Φ₀, ((‖φ x‖ : ℝ) : ℂ) ^ 2 * ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ) ∂μ := h3
    have hcast : ∀ θ : AdelicGL2 (𝓞 F) F → ℂ, ((∫ x in Φ₀, ‖θ x‖ ^ 2 * Wr x ∂μ : ℝ) : ℂ) =
        ∫ x in Φ₀, ((‖θ x‖ : ℝ) : ℂ) ^ 2 * ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ) ∂μ := by
      intro θ
      refine (integral_ofReal (𝕜 := ℂ) (f := fun x => ‖θ x‖ ^ 2 * Wr x)).symm.trans ?_
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      show (((‖θ x‖ ^ 2 * Wr x : ℝ)) : ℂ) = ((‖θ x‖ : ℝ) : ℂ) ^ 2 * ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
      push_cast
      rfl
    have hl := hcast (fun x => φ (x * y))
    have hr := hcast φ
    beta_reduce at hl
    apply Complex.ofReal_injective
    rw [Complex.ofReal_mul, hl, hr]
    exact h3'

  have hJint : ∀ x, Integrable (fun y => ‖φ (x * y)‖ ^ 2 * ‖g y‖) μ := fun x =>
    (((hφc.comp (continuous_const.mul continuous_id)).norm.pow 2).mul hg.norm).integrable_of_hasCompactSupport
      hgc.norm.mul_left
  have hJ_nonneg : ∀ x, 0 ≤ ∫ y, ‖φ (x * y)‖ ^ 2 * ‖g y‖ ∂μ := fun x =>
    integral_nonneg fun y => mul_nonneg (pow_nonneg (norm_nonneg _) 2) (norm_nonneg _)
  have hpt : ∀ x, ‖rightConv F φ g x‖ ^ 2 ≤ N1 * ∫ y, ‖φ (x * y)‖ ^ 2 * ‖g y‖ ∂μ := by
    intro x

    have hsg : Continuous fun y => Real.sqrt ‖g y‖ := Real.continuous_sqrt.comp hg.norm
    have hsg_supp : HasCompactSupport fun y => Real.sqrt ‖g y‖ :=
      hgc.norm.comp_left (g := Real.sqrt) Real.sqrt_zero
    have hf1 : Continuous fun y => ‖φ (x * y)‖ * Real.sqrt ‖g y‖ := (hφc.comp (continuous_const.mul continuous_id)).norm.mul hsg
    have hf1_supp : HasCompactSupport fun y => ‖φ (x * y)‖ * Real.sqrt ‖g y‖ := hsg_supp.mul_left
    have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) Real.HolderConjugate.two_two
      (ae_of_all _ fun y => mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
      (ae_of_all _ fun y => Real.sqrt_nonneg _)
      (by simpa using hf1.memLp_of_hasCompactSupport (μ := μ) (p := 2) hf1_supp)
      (by simpa using hsg.memLp_of_hasCompactSupport (μ := μ) (p := 2) hsg_supp)
    have hprod : ∀ y, (‖φ (x * y)‖ * Real.sqrt ‖g y‖) * Real.sqrt ‖g y‖ = ‖φ (x * y)‖ * ‖g y‖ := fun y => by
      rw [mul_assoc, Real.mul_self_sqrt (norm_nonneg _)]
    have hsq1 : ∀ y, (‖φ (x * y)‖ * Real.sqrt ‖g y‖) ^ (2 : ℝ) = ‖φ (x * y)‖ ^ 2 * ‖g y‖ := fun y => by
      rw [Real.rpow_two, mul_pow, Real.sq_sqrt (norm_nonneg _)]
    have hsq2 : ∀ y, (Real.sqrt ‖g y‖) ^ (2 : ℝ) = ‖g y‖ := fun y => by
      rw [Real.rpow_two, Real.sq_sqrt (norm_nonneg _)]
    simp only [hprod, hsq1, hsq2] at hCS
    have hle1 : ‖rightConv F φ g x‖ ≤ ∫ y, ‖φ (x * y)‖ * ‖g y‖ ∂μ := by
      rw [rightConv_apply]
      refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
      congr 1; funext y; rw [norm_mul]
    have hle2 : ‖rightConv F φ g x‖ ≤ (∫ y, ‖φ (x * y)‖ ^ 2 * ‖g y‖ ∂μ) ^ (1 / (2 : ℝ)) * N1 ^ (1 / (2 : ℝ)) :=
      hle1.trans hCS
    have h0 : 0 ≤ ‖rightConv F φ g x‖ := norm_nonneg _
    calc ‖rightConv F φ g x‖ ^ 2
        ≤ ((∫ y, ‖φ (x * y)‖ ^ 2 * ‖g y‖ ∂μ) ^ (1 / (2 : ℝ)) * N1 ^ (1 / (2 : ℝ))) ^ 2 :=
          pow_le_pow_left₀ h0 hle2 2
      _ = N1 * ∫ y, ‖φ (x * y)‖ ^ 2 * ‖g y‖ ∂μ := by
          rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (hJ_nonneg x), ← Real.rpow_mul hN1_nonneg]
          norm_num
          ring

  have hmeasF : Measurable fun p : AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F => ENNReal.ofReal (‖φ (p.1 * p.2)‖ ^ 2 * ‖g p.2‖ * Wr p.1) := by
    refine (Continuous.measurable ?_).ennreal_ofReal
    exact (((hφc.comp continuous_mul).norm.pow 2).mul (hg.comp continuous_snd).norm).mul (hWr_cont.comp continuous_fst)
  have hkey : ENNReal.ofReal (∫ x in Φ₀, ‖rightConv F φ g x‖ ^ 2 * Wr x ∂μ) ≤
      ENNReal.ofReal (N1 * N2 * ∫ x in Φ₀, ‖φ x‖ ^ 2 * Wr x ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hQint _ hA.1)
      (ae_of_all _ fun x => mul_nonneg (pow_nonneg (norm_nonneg _) 2) (hWr_nonneg x))]
    calc ∫⁻ x in Φ₀, ENNReal.ofReal (‖rightConv F φ g x‖ ^ 2 * Wr x) ∂μ
        ≤ ∫⁻ x in Φ₀, ENNReal.ofReal (N1 * (∫ y, ‖φ (x * y)‖ ^ 2 * ‖g y‖ ∂μ) * Wr x) ∂μ :=
          lintegral_mono fun x => ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hpt x) (hWr_nonneg x))
      _ = ∫⁻ x in Φ₀, ENNReal.ofReal N1 * ∫⁻ y, ENNReal.ofReal (‖φ (x * y)‖ ^ 2 * ‖g y‖ * Wr x) ∂μ ∂μ := by
          refine lintegral_congr fun x => ?_
          rw [mul_assoc, ENNReal.ofReal_mul hN1_nonneg, ← integral_mul_const,
            ofReal_integral_eq_lintegral_ofReal ((hJint x).mul_const _)
              (ae_of_all _ fun y => mul_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) 2) (norm_nonneg _)) (hWr_nonneg x))]
      _ = ENNReal.ofReal N1 * ∫⁻ x in Φ₀, ∫⁻ y, ENNReal.ofReal (‖φ (x * y)‖ ^ 2 * ‖g y‖ * Wr x) ∂μ ∂μ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal N1 * ∫⁻ y, ∫⁻ x in Φ₀, ENNReal.ofReal (‖φ (x * y)‖ ^ 2 * ‖g y‖ * Wr x) ∂μ ∂μ := by
          rw [lintegral_lintegral_swap hmeasF.aemeasurable]
      _ = ENNReal.ofReal N1 * ∫⁻ y, ENNReal.ofReal ‖g y‖ * ∫⁻ x in Φ₀, ENNReal.ofReal (‖φ (x * y)‖ ^ 2 * Wr x) ∂μ ∂μ := by
          congr 1
          refine lintegral_congr fun y => ?_
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun x => ?_
          rw [← ENNReal.ofReal_mul (norm_nonneg _)]
          congr 1; ring
      _ = ENNReal.ofReal N1 * ∫⁻ y, ENNReal.ofReal ‖g y‖ *
            ENNReal.ofReal (NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ σ * ∫ x in Φ₀, ‖φ x‖ ^ 2 * Wr x ∂μ) ∂μ := by
          congr 1
          refine lintegral_congr fun y => ?_
          rw [← ofReal_integral_eq_lintegral_ofReal (hQint _ (htrans y).1)
            (ae_of_all _ fun x => mul_nonneg (pow_nonneg (norm_nonneg _) 2) (hWr_nonneg x)), (htrans y).2]
      _ = ENNReal.ofReal N1 * ((∫⁻ y, ENNReal.ofReal (‖g y‖ * NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ σ) ∂μ) *
            ENNReal.ofReal (∫ x in Φ₀, ‖φ x‖ ^ 2 * Wr x ∂μ)) := by
          congr 1
          rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun y => ?_
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg (NumberField.TateGlobal.ideleNorm_pos _).le σ),
            ENNReal.ofReal_mul (norm_nonneg (g y)), mul_assoc]
      _ = ENNReal.ofReal (N1 * N2 * ∫ x in Φ₀, ‖φ x‖ ^ 2 * Wr x ∂μ) := by
          rw [← ofReal_integral_eq_lintegral_ofReal hg2_int
            (ae_of_all _ fun y => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (NumberField.TateGlobal.ideleNorm_pos _).le _)),
            ← ENNReal.ofReal_mul hN2_nonneg, ← ENNReal.ofReal_mul hN1_nonneg, mul_assoc]

  have hQφ_nonneg : 0 ≤ ∫ x in Φ₀, ‖φ x‖ ^ 2 * Wr x ∂μ :=
    integral_nonneg fun x => mul_nonneg (pow_nonneg (norm_nonneg _) 2) (hWr_nonneg x)
  have hreal : ∫ x in Φ₀, ‖rightConv F φ g x‖ ^ 2 * Wr x ∂μ ≤ N1 * N2 * ∫ x in Φ₀, ‖φ x‖ ^ 2 * Wr x ∂μ :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_nonneg hN1_nonneg hN2_nonneg) hQφ_nonneg)).mp hkey
  rw [← normsq _ hφg, ← normsq φ hφ.1] at hreal
  have h1 : ‖toCarrier F hΦ₀ σ ξ ⟨rightConv F φ g, hφg⟩‖ = Real.sqrt (‖toCarrier F hΦ₀ σ ξ ⟨rightConv F φ g, hφg⟩‖ ^ 2) :=
    (Real.sqrt_sq (norm_nonneg _)).symm
  rw [h1]
  calc Real.sqrt (‖toCarrier F hΦ₀ σ ξ ⟨rightConv F φ g, hφg⟩‖ ^ 2)
      ≤ Real.sqrt (N1 * N2 * ‖toCarrier F hΦ₀ σ ξ ⟨φ, hφ.1⟩‖ ^ 2) := Real.sqrt_le_sqrt hreal
    _ = Real.sqrt (N1 * N2) * ‖toCarrier F hΦ₀ σ ξ ⟨φ, hφ.1⟩‖ := by
        rw [Real.sqrt_mul (mul_nonneg hN1_nonneg hN2_nonneg), Real.sqrt_sq (norm_nonneg _)]

end S_AutomorphicForm_CuspidalSpectrum_exists_norm_toCarrier_rightConv_le
end P2MW
export P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_norm_toCarrier_rightConv_le (solution)
