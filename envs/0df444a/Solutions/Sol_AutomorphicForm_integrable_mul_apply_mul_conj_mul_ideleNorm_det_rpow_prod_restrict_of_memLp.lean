-- Prove2me | solution 1 for AutomorphicForm.integrable_mul_apply_mul_conj_mul_ideleNorm_det_rpow_prod_restrict_of_memLp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/0a02d620-a893-53b3-81c5-20f2c14c6289

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_PeterssonIntegral
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Integral.Prod
import Theorems.Thm_AutomorphicForm_exists_forall_memLp_two_comp_mul_right_restrict_and_eLpNorm_le_of_isFundamentalDomain
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integrable_mul_apply_mul_conj_mul_ideleNorm_det_rpow_prod_restrict_of_memLp
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

attribute [local instance] NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

noncomputable section

namespace FubInt43

open NumberField.TateGlobal

section General

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem integral_norm_sq_le_of_eLpNorm_le {φ : X → ℂ} (hφ : AEStronglyMeasurable φ μ) {C : ℝ≥0∞}
    (hC : C ≠ ∞) (h : eLpNorm φ 2 μ ≤ C) : ∫ a, ‖φ a‖ ^ 2 ∂μ ≤ (C ^ 2).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun a => sq_nonneg _)
    (hφ.norm.pow 2)]
  refine ENNReal.toReal_mono (ENNReal.pow_ne_top hC) ?_
  have hint : ∫⁻ a, ENNReal.ofReal (‖φ a‖ ^ 2) ∂μ = ∫⁻ a, ‖φ a‖ₑ ^ (2 : ℝ) ∂μ := by
    refine lintegral_congr fun a => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ← ENNReal.rpow_natCast]
    norm_num
  have hL : eLpNorm φ 2 μ = (∫⁻ a, ‖φ a‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat]
  rw [hint]
  have h2 : ((∫⁻ a, ‖φ a‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) ≤ C ^ (2 : ℝ) :=
    ENNReal.rpow_le_rpow (hL ▸ h) (by norm_num)
  rw [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one] at h2
  rw [← ENNReal.rpow_natCast]
  exact_mod_cast h2

end General

variable {F : Type} [Field F] [NumberField F]

abbrev dn (g : AdelicGL2 (𝓞 F) F) : ℝ := NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g)

theorem dn_pos (g : AdelicGL2 (𝓞 F) F) : 0 < dn g := ideleNorm_pos _

theorem continuous_dn : Continuous (fun g : AdelicGL2 (𝓞 F) F => dn g) :=
  NumberField.TateGlobal.continuous_ideleNorm_det F

theorem continuous_dn_rpow (s : ℝ) : Continuous (fun g : AdelicGL2 (𝓞 F) F => dn g ^ s) :=
  continuous_dn.rpow_const fun g => Or.inl (dn_pos g).ne'

theorem rpow_le_of_mem_slab {a b : ℝ} (ha : 0 < a) (s : ℝ) {g : AdelicGL2 (𝓞 F) F}
    (hg : dn g ∈ Set.Icc a b) : ‖dn g ^ s‖ ≤ max (a ^ s) (b ^ s) := by
  have h : a ≤ dn g ∧ dn g ≤ b := hg
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (dn_pos g).le s)]
  rcases le_or_gt 0 s with hs | hs
  · exact (Real.rpow_le_rpow (dn_pos g).le h.2 hs).trans (le_max_right _ _)
  · refine le_trans ?_ (le_max_left _ _)
    rw [← neg_neg s, Real.rpow_neg (dn_pos g).le, Real.rpow_neg ha.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos ha _) (Real.rpow_le_rpow ha.le h.1 (neg_nonneg.mpr hs.le))

theorem main
    (F : Type) [Field F] [NumberField F]
    [SigmaFinite (adelicGLHaar (Fin 2) (𝓞 F) F)]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Φ : AdelicGL2 (𝓞 F) F → ℂ) (χ : (AdeleRing (𝓞 F) F)ˣ → ℂ) (hχ : ∀ n, χ n ≠ 0)
    (hΦc : Continuous Φ)
    (hmem : MemLp Φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)))
    (hΓ : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (w : AdelicGL2 (𝓞 F) F), Φ (globalPoints (𝓞 F) F γ * w) = Φ w)
    (hZ : ∀ (n : (AdeleRing (𝓞 F) F)ˣ) (w : AdelicGL2 (𝓞 F) F), Φ (centralScalar (𝓞 F) F n * w) = χ n * Φ w)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (S : Set (AdelicGL2 (𝓞 F) F)) (hSm : MeasurableSet S) (hSs : S ⊆ {g : AdelicGL2 (𝓞 F) F | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hS : IsFundamentalDomain (globalPoints (𝓞 F) F).range S
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g : AdelicGL2 (𝓞 F) F | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hfc : Continuous f) (hfs : HasCompactSupport f)
    (Y : AdelicGL2 (𝓞 F) F → ℂ) (hYc : Continuous Y)
    (hY : MemLp Y 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S)) (w : ℝ) :
    Integrable (fun p : AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F =>
        Φ (p.1 * p.2) * f p.2 * (starRingEnd ℂ) (Y p.1) * ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det p.1) ^ (-w) : ℝ) : ℂ))
      (((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S).prod (adelicGLHaar (Fin 2) (𝓞 F) F)) ∧
    Integrable (fun p : AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F =>
        Y p.1 * (starRingEnd ℂ) (Φ (p.1 * p.2) * f p.2) * ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det p.1) ^ (-w) : ℝ) : ℂ))
      (((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S).prod (adelicGLHaar (Fin 2) (𝓞 F) F)) := by
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 F) F) := NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F

  obtain ⟨hTmem, hTbd⟩ :=
    AutomorphicForm.exists_forall_memLp_two_comp_mul_right_restrict_and_eLpNorm_le_of_isFundamentalDomain
      F c u d₁ d₂ T hd hcov Φ χ hχ hmem hΓ hZ α β hα hαβ S hSs hS

  set Cw : ℝ := max (α ^ (-w)) (β ^ (-w)) with hCw
  have hCw0 : 0 ≤ Cw := le_max_of_le_left (Real.rpow_nonneg hα.le _)
  have hwS : ∀ g ∈ S, ‖dn g ^ (-w)‖ ≤ Cw := fun g hg => rpow_le_of_mem_slab hα (-w) (hSs hg)

  set K : AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F → ℂ := fun p : AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F =>
        Φ (p.1 * p.2) * f p.2 * (starRingEnd ℂ) (Y p.1) * ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det p.1) ^ (-w) : ℝ) : ℂ) with hKdef
  set K' : AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F → ℂ := fun p : AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F =>
        Y p.1 * (starRingEnd ℂ) (Φ (p.1 * p.2) * f p.2) * ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det p.1) ^ (-w) : ℝ) : ℂ) with hK'def
  have hKc : Continuous K :=
    (((hΦc.comp continuous_mul).mul (hfc.comp continuous_snd)).mul
      (Complex.continuous_conj.comp (hYc.comp continuous_fst))).mul
      (Complex.continuous_ofReal.comp ((continuous_dn_rpow (-w)).comp continuous_fst))
  have hK'c : Continuous K' :=
    ((hYc.comp continuous_fst).mul (Complex.continuous_conj.comp
      ((hΦc.comp continuous_mul).mul (hfc.comp continuous_snd)))).mul
      (Complex.continuous_ofReal.comp ((continuous_dn_rpow (-w)).comp continuous_fst))
  have hKm : AEStronglyMeasurable K (((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S).prod (adelicGLHaar (Fin 2) (𝓞 F) F)) := hKc.aestronglyMeasurable
  have hK'm : AEStronglyMeasurable K' (((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S).prod (adelicGLHaar (Fin 2) (𝓞 F) F)) := hK'c.aestronglyMeasurable

  have hKnorm : ∀ g x, ‖K (g, x)‖ = ‖Φ (g * x)‖ * ‖f x‖ * ‖Y g‖ * ‖dn g ^ (-w)‖ := by
    intro g x
    simp only [hKdef, norm_mul, Complex.norm_conj, Complex.norm_real]
  have hK'norm : ∀ p, ‖K' p‖ = ‖K p‖ := by
    rintro ⟨g, x⟩
    rw [hKnorm]
    simp only [hK'def, norm_mul, Complex.norm_conj, Complex.norm_real]
    ring
  have hKbd : ∀ g ∈ S, ∀ x, ‖K (g, x)‖ ≤ ‖f x‖ * Cw * (‖Φ (g * x)‖ ^ 2 + ‖Y g‖ ^ 2) := by
    intro g hg x
    rw [hKnorm]
    have h1 : ‖Φ (g * x)‖ * ‖Y g‖ ≤ ‖Φ (g * x)‖ ^ 2 + ‖Y g‖ ^ 2 := by
      nlinarith [sq_nonneg (‖Φ (g * x)‖ - ‖Y g‖), norm_nonneg (Φ (g * x)), norm_nonneg (Y g)]
    calc ‖Φ (g * x)‖ * ‖f x‖ * ‖Y g‖ * ‖dn g ^ (-w)‖ = ‖f x‖ * ‖dn g ^ (-w)‖ * (‖Φ (g * x)‖ * ‖Y g‖) := by ring
      _ ≤ ‖f x‖ * Cw * (‖Φ (g * x)‖ ^ 2 + ‖Y g‖ ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hwS g hg) (norm_nonneg _)) h1
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (mul_nonneg (norm_nonneg _) hCw0)

  have hY2 : Integrable (fun g => ‖Y g‖ ^ 2) ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S) := (memLp_two_iff_integrable_sq_norm hY.1).mp hY
  have hΦ2 : ∀ x, Integrable (fun g => ‖Φ (g * x)‖ ^ 2) ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S) := fun x =>
    (memLp_two_iff_integrable_sq_norm (hTmem x).1).mp (hTmem x)

  have hsec : ∀ x, Integrable (fun g => K (g, x)) ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S) := by
    intro x
    refine Integrable.mono' (((hΦ2 x).add hY2).const_mul (‖f x‖ * Cw))
      (hKc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hSm] with g hg
    simpa only [Pi.add_apply] using hKbd g hg x

  obtain ⟨Bf, hBf⟩ : ∃ B : ℝ, ∀ x, ‖f x‖ ≤ B := by
    obtain ⟨R, hR⟩ := (hfs.isCompact_range hfc).isBounded.exists_norm_le
    exact ⟨R, fun x => hR _ ⟨x, rfl⟩⟩
  have hBf0 : 0 ≤ Bf := (norm_nonneg _).trans (hBf 1)
  set IY : ℝ := ∫ g, ‖Y g‖ ^ 2 ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S) with hIY
  have hIY0 : 0 ≤ IY := integral_nonneg fun _ => sq_nonneg _
  have hh0 : ∀ x, 0 ≤ ∫ g, ‖K (g, x)‖ ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S) := fun x => integral_nonneg fun _ => norm_nonneg _
  have hhle : ∀ x, ∫ g, ‖K (g, x)‖ ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S) ≤ ‖f x‖ * Cw * (∫ g, ‖Φ (g * x)‖ ^ 2 ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S) + IY) := by
    intro x
    calc ∫ g, ‖K (g, x)‖ ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S)
        ≤ ∫ g, ‖f x‖ * Cw * (‖Φ (g * x)‖ ^ 2 + ‖Y g‖ ^ 2) ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S) := by
          refine integral_mono_ae (hsec x).norm (((hΦ2 x).add hY2).const_mul (‖f x‖ * Cw)) ?_
          filter_upwards [ae_restrict_mem hSm] with g hg
          exact hKbd g hg x
      _ = ‖f x‖ * Cw * (∫ g, ‖Φ (g * x)‖ ^ 2 ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S) + IY) := by
          rw [integral_const_mul, integral_add (hΦ2 x) hY2]
  have hhm : AEStronglyMeasurable (fun x => ∫ g, ‖K (g, x)‖ ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S)) (adelicGLHaar (Fin 2) (𝓞 F) F) := by
    simpa using hKm.prod_swap.norm.integral_prod_right'
  have hzero : ∀ x, x ∉ tsupport f → ∀ g, K (g, x) = 0 := by
    intro x hx g
    simp only [hKdef, image_eq_zero_of_notMem_tsupport hx, mul_zero, zero_mul]

  have hint2 : Integrable (fun x => ∫ g, ‖K (g, x)‖ ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S)) (adelicGLHaar (Fin 2) (𝓞 F) F) := by
    by_cases hne : (tsupport f).Nonempty
    · obtain ⟨xm, hxm, hmin⟩ := hfs.isCompact.exists_isMinOn hne continuous_dn.continuousOn
      obtain ⟨xM, hxM, hmax⟩ := hfs.isCompact.exists_isMaxOn hne continuous_dn.continuousOn
      have ha : 0 < dn xm := dn_pos xm
      have hab : dn xm ≤ dn xM := hmin hxM
      obtain ⟨C, hCtop, hC⟩ := hTbd (dn xm) (dn xM) ha hab
      have hΦbd : ∀ x ∈ tsupport f, ∫ g, ‖Φ (g * x)‖ ^ 2 ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S) ≤ (C ^ 2).toReal := fun x hx =>
        integral_norm_sq_le_of_eLpNorm_le (hTmem x).1 hCtop (hC x ⟨hmin hx, hmax hx⟩)
      set M : ℝ := Bf * Cw * ((C ^ 2).toReal + IY) with hM
      have hbound : ∀ x, ‖∫ g, ‖K (g, x)‖ ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S)‖ ≤ (tsupport f).indicator (fun _ => M) x := by
        intro x
        rw [Real.norm_of_nonneg (hh0 x)]
        by_cases hx : x ∈ tsupport f
        · rw [Set.indicator_of_mem hx]
          refine (hhle x).trans ?_
          exact mul_le_mul (mul_le_mul_of_nonneg_right (hBf x) hCw0) (by linarith [hΦbd x hx])
            (by positivity) (mul_nonneg hBf0 hCw0)
        · rw [Set.indicator_of_notMem hx]
          have : (fun g => ‖K (g, x)‖) = fun _ => 0 := funext fun g => by rw [hzero x hx g, norm_zero]
          rw [this, integral_zero]
      have hind : Integrable ((tsupport f).indicator fun _ => M) (adelicGLHaar (Fin 2) (𝓞 F) F) :=
        (integrableOn_const (hfs.isCompact.measure_lt_top).ne).integrable_indicator
          (isClosed_tsupport f).measurableSet
      exact hind.mono' hhm (Filter.Eventually.of_forall hbound)
    · have hall : ∀ x, x ∉ tsupport f := fun x hx => hne ⟨x, hx⟩
      have : (fun x => ∫ g, ‖K (g, x)‖ ∂((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S)) = fun _ => 0 := by
        funext x
        have : (fun g => ‖K (g, x)‖) = fun _ => 0 := funext fun g => by rw [hzero x (hall x) g, norm_zero]
        rw [this, integral_zero]
      rw [this]
      exact integrable_zero _ _ _
  have hK1 : Integrable K (((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S).prod (adelicGLHaar (Fin 2) (𝓞 F) F)) :=
    (integrable_prod_iff' hKm).mpr ⟨Filter.Eventually.of_forall hsec, hint2⟩
  exact ⟨hK1, hK1.norm.mono' hK'm (Filter.Eventually.of_forall fun p => (hK'norm p).le)⟩

end FubInt43

end

theorem solution
    (F : Type) [Field F] [NumberField F]
    [SigmaFinite (adelicGLHaar (Fin 2) (𝓞 F) F)]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) (_hd : d₁ < d₂)
    (_hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Φ : AdelicGL2 (𝓞 F) F → ℂ) (χ : (AdeleRing (𝓞 F) F)ˣ → ℂ) (_hχ : ∀ n, χ n ≠ 0)
    (_hΦc : Continuous Φ)
    (_hmem : MemLp Φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)))
    (_hΓ : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (w : AdelicGL2 (𝓞 F) F), Φ (globalPoints (𝓞 F) F γ * w) = Φ w)
    (_hZ : ∀ (n : (AdeleRing (𝓞 F) F)ˣ) (w : AdelicGL2 (𝓞 F) F), Φ (centralScalar (𝓞 F) F n * w) = χ n * Φ w)
    (α β : ℝ) (_hα : 0 < α) (_hαβ : α < β)
    (S : Set (AdelicGL2 (𝓞 F) F)) (_hSm : MeasurableSet S) (_hSs : S ⊆ {g : AdelicGL2 (𝓞 F) F | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (_hS : IsFundamentalDomain (globalPoints (𝓞 F) F).range S
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g : AdelicGL2 (𝓞 F) F | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (f : AdelicGL2 (𝓞 F) F → ℂ) (_hfc : Continuous f) (_hfs : HasCompactSupport f)
    (Y : AdelicGL2 (𝓞 F) F → ℂ) (_hYc : Continuous Y)
    (_hY : MemLp Y 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S)) (w : ℝ) :
    Integrable (fun p : AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F =>
        Φ (p.1 * p.2) * f p.2 * (starRingEnd ℂ) (Y p.1) * ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det p.1) ^ (-w) : ℝ) : ℂ))
      (((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S).prod (adelicGLHaar (Fin 2) (𝓞 F) F)) ∧
    Integrable (fun p : AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F =>
        Y p.1 * (starRingEnd ℂ) (Φ (p.1 * p.2) * f p.2) * ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det p.1) ^ (-w) : ℝ) : ℂ))
      (((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S).prod (adelicGLHaar (Fin 2) (𝓞 F) F)) :=
  FubInt43.main F c u d₁ d₂ T _hd _hcov Φ χ _hχ _hΦc _hmem _hΓ _hZ α β _hα _hαβ S _hSm _hSs _hS f _hfc _hfs Y _hYc _hY w

end S_AutomorphicForm_integrable_mul_apply_mul_conj_mul_ideleNorm_det_rpow_prod_restrict_of_memLp
end P2MW
export P2MW.S_AutomorphicForm_integrable_mul_apply_mul_conj_mul_ideleNorm_det_rpow_prod_restrict_of_memLp (solution)
