-- Prove2me | solution 1 for AutomorphicForm.peterssonIntegral_mul_bruhatEisenstein_eq_integral_whittakerCoefficient_mul_conj_rationalCentreUnipotentQuotient_of_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/466087fb-062b-56f2-ab0c-1940eb3c648c

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_PeterssonIntegral
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_RationalCentreUnipotentQuotient
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Theorems.Thm_MeasureTheory_IsFundamentalDomain_iUnion_inv_smul_of_leftCosetRepresentatives
import Theorems.Thm_MeasureTheory_IsFundamentalDomain_setLIntegral_iUnion_inv_smul_eq_and_setIntegral_eq_of_leftCosetRepresentatives
import Theorems.Thm_HaarQuotient_integrable_setIntegral_mul_out_and_setIntegral_eq_integral_setIntegral_mul_out
import Theorems.Thm_AutomorphicForm_existsUnique_bruhatRepresentative_mul_mem_borelSubgroup
import Theorems.Thm_AutomorphicForm_existsUnique_diagOne_inv_mul_mem_scalar_sup_unipotent_of_mem_borelSubgroup
import Theorems.Thm_AutomorphicForm_IsInducedSection_apply_globalPoints_mul_of_mem_borelSubgroup_and_apply_unipotentGL2_mul
import Theorems.Thm_AutomorphicForm_isClosed_rationalTorusUnipotent
import Theorems.Thm_AutomorphicForm_isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant
import Theorems.Thm_AutomorphicForm_isFundamentalDomain_boxSheet_rationalCentreUnipotent
import Theorems.Thm_AutomorphicForm_isFundamentalDomain_boxSheet_rationalTorusUnipotent
import Theorems.Thm_AutomorphicForm_sum_norm_whittakerCoefficient_sq_le_integral_norm_sq
import Theorems.Thm_NumberField_AdelicBox_setLIntegral_adelicBox_comp_mul_add_eq_of_periodic
import Theorems.Thm_AutomorphicForm_integral_mul_conj_unipotent_eq_tsum_units_whittakerCoefficient_one_diagOne_and_tsum_norm_le
import Theorems.Thm_HaarQuotient_setLIntegral_eq_lintegral_setLIntegral_mul_out
import Theorems.Thm_AutomorphicForm_integral_mul_conj_eq_tsum_whittakerCoefficient_mul_conj
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_unipotentGL2_mul
import Theorems.Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_AutomorphicForm_isClosed_rationalCentreUnipotent
import Theorems.Thm_AutomorphicForm_isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Theorems.Thm_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range
import Theorems.Thm_AutomorphicForm_integral_rationalTorusUnipotentQuotient_tsum_units_eq_integral_rationalCentreUnipotentQuotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_peterssonIntegral_mul_bruhatEisenstein_eq_integral_whittakerCoefficient_mul_conj_rationalCentreUnipotentQuotient_of_integrable
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_peterssonIntegral_mul_bruhatEisenstein_eq_integral_whittakerCoefficient_mul_conj_rationalCentreUnipotentQuotient_of_integrable.AutomorphicForm IsDedekindDomain NumberField.TateGlobal"
open scoped NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

noncomputable section

namespace RS11C9A

open scoped Pointwise ENNReal

variable (F : Type) [Field F] [NumberField F]

scoped instance countable_numberField : Countable F :=
  (Module.finBasis ℚ F).equivFun.toEquiv.injective.countable

scoped instance countable_matrix : Countable (Matrix (Fin 2) (Fin 2) F) :=
  inferInstanceAs (Countable (Fin 2 → Fin 2 → F))

scoped instance countable_gl2 : Countable (Matrix.GeneralLinearGroup (Fin 2) F) :=
  Units.val_injective.countable

@[reducible] def mGL : MeasurableSpace (Matrix.GeneralLinearGroup (Fin 2) F) := ⊤

@[reducible] def ratAction : MulAction (Matrix.GeneralLinearGroup (Fin 2) F) (AdelicGL2 (𝓞 F) F) :=
  MulAction.compHom _ (globalPoints (𝓞 F) F)

attribute [local instance] ratAction

theorem rat_smul_def (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F) :
    γ • g = globalPoints (𝓞 F) F γ * g := rfl

theorem measurableSMul_rat : @MeasurableSMul (Matrix.GeneralLinearGroup (Fin 2) F) (AdelicGL2 (𝓞 F) F) _ (mGL F) _ := by
  letI := mGL F
  exact
    { measurable_const_smul := fun γ => by
        show Measurable fun g : AdelicGL2 (𝓞 F) F => globalPoints (𝓞 F) F γ * g
        exact measurable_const_mul _
      measurable_smul_const := fun g => measurable_from_top }

scoped instance smulInvariant_rat : SMulInvariantMeasure (Matrix.GeneralLinearGroup (Fin 2) F) (AdelicGL2 (𝓞 F) F)
    (adelicGLHaar (Fin 2) (𝓞 F) F) := by
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  refine ⟨fun γ s hs => ?_⟩
  show adelicGLHaar (Fin 2) (𝓞 F) F ((fun g => globalPoints (𝓞 F) F γ * g) ⁻¹' s) = _
  exact measure_preimage_mul (adelicGLHaar (Fin 2) (𝓞 F) F) (globalPoints (𝓞 F) F γ) s

private def _root_.RS11C9A.slab (d₁ d₂ : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}

p2m_export "RS11C9A" "slab"
private theorem _root_.RS11C9A.measurableSet_slab (d₁ d₂ : ℝ) : MeasurableSet (slab F d₁ d₂) :=
  NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc F d₁ d₂

p2m_export "RS11C9A" "measurableSet_slab"
theorem globalPoints_mul_mem_slab_iff {d₁ d₂ : ℝ} (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F) :
    globalPoints (𝓞 F) F γ * g ∈ slab F d₁ d₂ ↔ g ∈ slab F d₁ d₂ := by
  simp only [slab, Set.mem_setOf_eq, map_mul, NumberField.TateGlobal.ideleNorm_mul,
    AutomorphicForm.ideleNorm_det_globalPoints, one_mul]

theorem preimage_slab {d₁ d₂ : ℝ} (γ : Matrix.GeneralLinearGroup (Fin 2) F) :
    (fun g => globalPoints (𝓞 F) F γ * g) ⁻¹' slab F d₁ d₂ = slab F d₁ d₂ := by
  ext g; exact globalPoints_mul_mem_slab_iff F γ g

scoped instance smulInvariant_rat_restrict (d₁ d₂ : ℝ) :
    SMulInvariantMeasure (Matrix.GeneralLinearGroup (Fin 2) F) (AdelicGL2 (𝓞 F) F)
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F d₁ d₂)) := by
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  refine ⟨fun γ s hs => ?_⟩
  have hs' : MeasurableSet ((fun g : AdelicGL2 (𝓞 F) F => globalPoints (𝓞 F) F γ * g) ⁻¹' s) :=
    (measurable_const_mul (globalPoints (𝓞 F) F γ)) hs
  show (adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F d₁ d₂) ((fun g => globalPoints (𝓞 F) F γ * g) ⁻¹' s) = _
  rw [Measure.restrict_apply hs', Measure.restrict_apply hs]
  have hset : (fun g : AdelicGL2 (𝓞 F) F => globalPoints (𝓞 F) F γ * g) ⁻¹' s ∩ slab F d₁ d₂ =
      (fun g : AdelicGL2 (𝓞 F) F => globalPoints (𝓞 F) F γ * g) ⁻¹' (s ∩ slab F d₁ d₂) := by
    rw [Set.preimage_inter, preimage_slab F γ]
  rw [hset]
  exact measure_preimage_mul (adelicGLHaar (Fin 2) (𝓞 F) F) (globalPoints (𝓞 F) F γ) (s ∩ slab F d₁ d₂)

scoped instance smulInvariant_range_restrict (d₁ d₂ : ℝ) :
    SMulInvariantMeasure (globalPoints (𝓞 F) F).range (AdelicGL2 (𝓞 F) F)
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F d₁ d₂)) := by
  refine ⟨fun γ s hs => ?_⟩
  obtain ⟨γ₀, hγ₀⟩ := γ.2
  have := (smulInvariant_rat_restrict F d₁ d₂).measure_preimage_smul γ₀ hs
  have hγ : (fun g : AdelicGL2 (𝓞 F) F => γ • g) = fun g => γ₀ • g := by
    funext g
    show (γ : AdelicGL2 (𝓞 F) F) * g = globalPoints (𝓞 F) F γ₀ * g
    rw [hγ₀]
  rw [hγ]
  exact this

theorem globalPoints_injective : Function.Injective (globalPoints (𝓞 F) F) := by
  intro a b h
  apply Units.ext
  ext i j
  have hij := congrArg (fun g : AdelicGL2 (𝓞 F) F => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j) h
  simp only [globalPoints, Matrix.GeneralLinearGroup.map_apply] at hij
  exact NumberField.AdeleRing.algebraMap_injective (𝓞 F) F hij

theorem isFundamentalDomain_top_of_range {S : Set (AdelicGL2 (𝓞 F) F)} {μ : Measure (AdelicGL2 (𝓞 F) F)}
    (hS : IsFundamentalDomain (globalPoints (𝓞 F) F).range S μ) :
    IsFundamentalDomain (⊤ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) F)) S μ := by
  have hinj := globalPoints_injective F
  let e : (⊤ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) F)) ≃ (globalPoints (𝓞 F) F).range :=
    Subgroup.topEquiv.toEquiv.trans (MonoidHom.ofInjective hinj).toEquiv
  have h := hS.image_of_equiv (ν := μ) (Equiv.refl _)
    (by exact (MeasurePreserving.id μ).quasiMeasurePreserving) e (fun γ g => ?_)
  · simpa using h
  · show ((MonoidHom.ofInjective hinj (Subgroup.topEquiv γ) : (globalPoints (𝓞 F) F).range) : AdelicGL2 (𝓞 F) F) * g =
      globalPoints (𝓞 F) F (γ : Matrix.GeneralLinearGroup (Fin 2) F) * g
    rw [MonoidHom.ofInjective_apply]
    rfl

theorem isFundamentalDomain_map_of {Q : Subgroup (Matrix.GeneralLinearGroup (Fin 2) F)}
    {S : Set (AdelicGL2 (𝓞 F) F)} {μ : Measure (AdelicGL2 (𝓞 F) F)}
    (hS : IsFundamentalDomain Q S μ) :
    IsFundamentalDomain (Q.map (globalPoints (𝓞 F) F)) S μ := by
  have hinj := globalPoints_injective F
  let e : Q.map (globalPoints (𝓞 F) F) ≃ Q := (Subgroup.equivMapOfInjective Q _ hinj).symm.toEquiv
  have h := hS.image_of_equiv (ν := μ) (Equiv.refl _)
    (by exact (MeasurePreserving.id μ).quasiMeasurePreserving) e (fun γ g => ?_)
  · simpa using h
  · show globalPoints (𝓞 F) F (((Subgroup.equivMapOfInjective Q _ hinj).symm γ : Q) : Matrix.GeneralLinearGroup (Fin 2) F) * g =
      (γ : AdelicGL2 (𝓞 F) F) * g
    congr 1
    have h1 := Subgroup.coe_equivMapOfInjective_apply Q (globalPoints (𝓞 F) F) hinj
      ((Subgroup.equivMapOfInjective Q _ hinj).symm γ)
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1.symm

theorem isFundamentalDomain_restrict {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X]
    {s : Set X} {μ : Measure X} (h : IsFundamentalDomain G s μ) (t : Set X) :
    IsFundamentalDomain G s (μ.restrict t) :=
  ⟨h.nullMeasurableSet.mono_ac (Measure.absolutelyContinuous_of_le Measure.restrict_le_self),
    ae_restrict_of_ae h.ae_covers,
    fun a b hab => by
      have h0 := h.aedisjoint hab
      unfold AEDisjoint at h0 ⊢
      exact le_antisymm ((Measure.le_iff'.mp Measure.restrict_le_self _).trans h0.le) bot_le⟩

private scoped instance _root_.RS11C9A.countable_range : Countable (globalPoints (𝓞 F) F).range := by
  have h : Countable (Set.range (globalPoints (𝓞 F) F)) := (Set.countable_range _).to_subtype
  exact h

p2m_export "RS11C9A" "countable_range"

scoped instance smulInvariant_range :
    SMulInvariantMeasure (globalPoints (𝓞 F) F).range (AdelicGL2 (𝓞 F) F) (adelicGLHaar (Fin 2) (𝓞 F) F) := by
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  refine ⟨fun γ s hs => ?_⟩
  show adelicGLHaar (Fin 2) (𝓞 F) F ((fun g => (γ : AdelicGL2 (𝓞 F) F) * g) ⁻¹' s) = _
  exact measure_preimage_mul (adelicGLHaar (Fin 2) (𝓞 F) F) (γ : AdelicGL2 (𝓞 F) F) s

theorem smul_slab_subset {d₁ d₂ : ℝ} (γ : (globalPoints (𝓞 F) F).range) {A : Set (AdelicGL2 (𝓞 F) F)}
    (hA : A ⊆ slab F d₁ d₂) : γ • A ⊆ slab F d₁ d₂ := by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨γ₀, hγ₀⟩ := γ.2
  show (γ : AdelicGL2 (𝓞 F) F) * a ∈ slab F d₁ d₂
  rw [← hγ₀]
  exact (globalPoints_mul_mem_slab_iff F γ₀ a).mpr (hA ha)

theorem smul_compl_slab_subset {d₁ d₂ : ℝ} (γ : (globalPoints (𝓞 F) F).range) {A : Set (AdelicGL2 (𝓞 F) F)}
    (hA : A ⊆ (slab F d₁ d₂)ᶜ) : γ • A ⊆ (slab F d₁ d₂)ᶜ := by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨γ₀, hγ₀⟩ := γ.2
  show (γ : AdelicGL2 (𝓞 F) F) * a ∉ slab F d₁ d₂
  rw [← hγ₀, globalPoints_mul_mem_slab_iff F γ₀ a]
  exact hA ha

theorem isFundamentalDomain_union_slab {d₁ d₂ : ℝ} {𝓕 D : Set (AdelicGL2 (𝓞 F) F)}
    (h𝓕s : 𝓕 ⊆ slab F d₁ d₂)
    (h𝓕 : IsFundamentalDomain (globalPoints (𝓞 F) F).range 𝓕 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F d₁ d₂)))
    (hD : IsFundamentalDomain (globalPoints (𝓞 F) F).range D (adelicGLHaar (Fin 2) (𝓞 F) F)) :
    IsFundamentalDomain (globalPoints (𝓞 F) F).range (𝓕 ∪ (D \ slab F d₁ d₂)) (adelicGLHaar (Fin 2) (𝓞 F) F) := by
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  set μ := adelicGLHaar (Fin 2) (𝓞 F) F with hμ
  set Sd := slab F d₁ d₂ with hSd
  have hSdm : MeasurableSet Sd := measurableSet_slab F d₁ d₂

  have h𝓕nm : NullMeasurableSet 𝓕 μ := by
    obtain ⟨t, ht_sub, htm, hteq⟩ := h𝓕.nullMeasurableSet.exists_measurable_subset_ae_eq

    have h0 : μ.restrict Sd (𝓕 \ t) = 0 := (ae_eq_set.mp hteq.symm).1
    have h0' : μ (𝓕 \ t) = 0 := by
      have hsub : 𝓕 \ t ⊆ Sd := fun x hx => h𝓕s hx.1
      rwa [Measure.restrict_apply' hSdm, Set.inter_eq_self_of_subset_left hsub] at h0
    have hae : (t : Set _) =ᵐ[μ] 𝓕 := by
      rw [ae_eq_set]
      refine ⟨?_, h0'⟩
      rw [Set.diff_eq_empty.mpr ht_sub]; exact measure_empty
    exact htm.nullMeasurableSet.congr hae
  refine ⟨h𝓕nm.union (hD.nullMeasurableSet.diff hSdm.nullMeasurableSet), ?_, ?_⟩
  ·
    have h1 : ∀ᵐ x ∂μ, x ∈ Sd → ∃ γ : (globalPoints (𝓞 F) F).range, γ • x ∈ 𝓕 := by
      rw [← ae_restrict_iff' hSdm]
      exact h𝓕.ae_covers
    filter_upwards [h1, hD.ae_covers] with x hx1 hx2
    by_cases hx : x ∈ Sd
    · obtain ⟨γ, hγ⟩ := hx1 hx
      exact ⟨γ, Or.inl hγ⟩
    · obtain ⟨γ, hγ⟩ := hx2
      refine ⟨γ, Or.inr ⟨hγ, ?_⟩⟩
      have := smul_compl_slab_subset F γ (A := {x}) (by simpa using hx)
      exact this (Set.smul_mem_smul_set rfl)
  ·
    intro a b hab
    have hF := h𝓕.aedisjoint hab
    have hDd := hD.aedisjoint hab
    simp only [Function.onFun] at hF hDd ⊢
    rw [Set.smul_set_union, Set.smul_set_union]
    refine AEDisjoint.union_left ?_ ?_ <;> refine AEDisjoint.union_right ?_ ?_
    ·
      unfold AEDisjoint at hF ⊢
      have hsub : a • 𝓕 ∩ b • 𝓕 ⊆ Sd := fun x hx => smul_slab_subset F a h𝓕s hx.1
      rwa [Measure.restrict_apply' hSdm, Set.inter_eq_self_of_subset_left hsub] at hF
    ·
      refine (Set.disjoint_iff_inter_eq_empty.mpr ?_).aedisjoint
      ext x; constructor
      · rintro ⟨hx1, hx2⟩
        exact (smul_compl_slab_subset F b (A := D \ Sd) (fun x hx => hx.2) hx2) (smul_slab_subset F a h𝓕s hx1)
      · intro hx; exact hx.elim
    · refine (Set.disjoint_iff_inter_eq_empty.mpr ?_).aedisjoint
      ext x; constructor
      · rintro ⟨hx1, hx2⟩
        exact (smul_compl_slab_subset F a (A := D \ Sd) (fun x hx => hx.2) hx1) (smul_slab_subset F b h𝓕s hx2)
      · intro hx; exact hx.elim
    · exact measure_mono_null (Set.inter_subset_inter (Set.smul_set_mono Set.diff_subset) (Set.smul_set_mono Set.diff_subset)) hDd

theorem isFundamentalDomain_of_ae_eq {G α : Type*} [Group G] [Countable G] [MulAction G α] [MeasurableSpace α]
    [MeasurableSpace G] [MeasurableSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ] {s t : Set α}
    (hs : IsFundamentalDomain G s μ) (hst : s =ᵐ[μ] t) (ht : NullMeasurableSet t μ) :
    IsFundamentalDomain G t μ := by
  have hg : ∀ g : G, g • s =ᵐ[μ] g • t := fun g => by
    have := ((measurePreserving_smul g⁻¹ μ).quasiMeasurePreserving).preimage_ae_eq hst
    rwa [Set.preimage_smul_inv, Set.preimage_smul_inv] at this
  refine ⟨ht, ?_, ?_⟩
  · have h1 := hs.ae_covers
    have h2 : ∀ᵐ x ∂μ, ∀ g : G, x ∈ g⁻¹ • s ↔ x ∈ g⁻¹ • t := by
      rw [ae_all_iff]
      intro g
      exact (hg g⁻¹).mem_iff
    filter_upwards [h1, h2] with x hx1 hx2
    obtain ⟨g, hgx⟩ := hx1
    refine ⟨g, ?_⟩
    have := (hx2 g).1 (Set.mem_inv_smul_set_iff.mpr hgx)
    exact Set.mem_inv_smul_set_iff.mp this
  · intro a b hab
    have hs' := hs.aedisjoint hab
    exact hs'.congr (hg a).symm (hg b).symm

theorem hasSum_option {M ι : Type*} [AddCommMonoid M] [TopologicalSpace M] [ContinuousAdd M]
    (g : Option ι → M) {a : M} (h : HasSum (fun i => g (some i)) a) : HasSum g (g none + a) := by
  set e := Equiv.optionEquivSumPUnit.{0} ι with he
  have h1 : HasSum ((g ∘ e.symm) ∘ Sum.inl) a := by
    have : ((g ∘ e.symm) ∘ Sum.inl) = fun i => g (some i) := by
      funext i; simp [he]
    rw [this]; exact h
  have h2 : HasSum ((g ∘ e.symm) ∘ Sum.inr) (g none) := by
    have : ((g ∘ e.symm) ∘ Sum.inr) = fun _ => g none := by
      funext u; simp [he]
    rw [this]
    simpa using hasSum_fintype (fun _ : PUnit.{1} => g none)
  have h3 := h1.sum h2
  rw [add_comm] at h3
  exact (e.symm.hasSum_iff).mp h3

theorem tsum_option_ennreal {ι : Type*} (g : Option ι → ℝ≥0∞) : ∑' o, g o = g none + ∑' i, g (some i) :=
  (hasSum_option g ENNReal.summable.hasSum).tsum_eq

private theorem _root_.RS11C9A.globalPoints_unipotentGL2 (β : F) :
    globalPoints (𝓞 F) F (unipotentGL2 β) = unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) := by
  apply Units.ext
  ext i j
  rw [globalPoints_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

p2m_export "RS11C9A" "globalPoints_unipotentGL2"
theorem globalPoints_bruhat (ξ : F) :
    globalPoints (𝓞 F) F ((gl2Weyl : Matrix.GeneralLinearGroup (Fin 2) F) * unipotentGL2 ξ) =
      adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) := by
  rw [map_mul, globalPoints_unipotentGL2]; rfl

theorem enorm_coe_real_of_nonneg {r : ℝ} (hr : 0 ≤ r) : ‖(r : ℂ)‖ₑ = ENNReal.ofReal r := by
  rw [enorm_eq_nnnorm, Complex.nnnorm_real, ← enorm_eq_nnnorm, Real.enorm_eq_ofReal hr]

theorem mul_le_sq_add_sq (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with h | h
  · calc a * b ≤ b * b := mul_le_mul_left h b
      _ = b ^ 2 := (sq b).symm
      _ ≤ a ^ 2 + b ^ 2 := le_add_self
  · calc a * b ≤ a * a := mul_le_mul_right h a
      _ = a ^ 2 := (sq a).symm
      _ ≤ a ^ 2 + b ^ 2 := le_self_add

theorem ofReal_sq_norm (z : ℂ) : ENNReal.ofReal (‖z‖ ^ 2) = ‖z‖ₑ ^ 2 := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

private theorem _root_.RS11C9A.indicator_comp_globalPoints_mul {β : Type*} [Zero β] {d₁ d₂ : ℝ} (γ : Matrix.GeneralLinearGroup (Fin 2) F)
    (f : AdelicGL2 (𝓞 F) F → β) (g : AdelicGL2 (𝓞 F) F) :
    (slab F d₁ d₂).indicator f (globalPoints (𝓞 F) F γ * g) =
      (slab F d₁ d₂).indicator (fun g => f (globalPoints (𝓞 F) F γ * g)) g := by
  by_cases hg : g ∈ slab F d₁ d₂
  · rw [Set.indicator_of_mem hg, Set.indicator_of_mem ((globalPoints_mul_mem_slab_iff F γ g).mpr hg)]
  · rw [Set.indicator_of_notMem hg,
      Set.indicator_of_notMem (fun h => hg ((globalPoints_mul_mem_slab_iff F γ g).mp h))]

p2m_export "RS11C9A" "indicator_comp_globalPoints_mul"

theorem tsum_indicator_const_set {ι β : Type*} [AddCommMonoid β] [TopologicalSpace β] (s : Set (AdelicGL2 (𝓞 F) F))
    (f : ι → AdelicGL2 (𝓞 F) F → β) (g : AdelicGL2 (𝓞 F) F) :
    ∑' i, s.indicator (f i) g = s.indicator (fun g => ∑' i, f i g) g := by
  by_cases hg : g ∈ s
  · simp only [Set.indicator_of_mem hg]
  · simp only [Set.indicator_of_notMem hg, tsum_zero]

end RS11C9A
p2m_reactivate "P2MW.S_AutomorphicForm_peterssonIntegral_mul_bruhatEisenstein_eq_integral_whittakerCoefficient_mul_conj_rationalCentreUnipotentQuotient_of_integrable.RS11C9A"

end
p2m_reactivate "P2MW.S_AutomorphicForm_peterssonIntegral_mul_bruhatEisenstein_eq_integral_whittakerCoefficient_mul_conj_rationalCentreUnipotentQuotient_of_integrable.RS11C9A"

open scoped Pointwise ENNReal

open Filter Topology
open scoped ENNReal NNReal Pointwise

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsInducedSection borelSubgroup mem_borelSubgroup_iff borelDiagFst borelDiagSnd unipotentGL2_mem_borelSubgroup globalPoints_apply AdelicGL2 globalPoints IsIdeleClassChar IsUnitaryChar unipotentGL2 unipotentGL2_coe unipotentGL2_zero unipotentGL2_add unipotentGL2Hom etaFst etaSnd gl2Weyl adelicWeyl peterssonIntegral productionPinsOf IsGlobalAddChar whittakerCoefficient rationalCentre rationalCentreUnipotent RationalCentreUnipotentQuotient rationalCentreUnipotentHaar rationalCentreUnipotentQuotientMeasure adelicUnipotent toAdelicUnipotent rationalTorus rationalTorusUnipotent rationalTorusUnipotentHaar existsUnique_bruhatRepresentative_mul_mem_borelSubgroup existsUnique_diagOne_inv_mul_mem_scalar_sup_unipotent_of_mem_borelSubgroup IsInducedSection.apply_globalPoints_mul_of_mem_borelSubgroup_and_apply_unipotentGL2_mul isClosed_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant isFundamentalDomain_boxSheet_rationalCentreUnipotent isFundamentalDomain_boxSheet_rationalTorusUnipotent integral_mul_conj_unipotent_eq_tsum_units_whittakerCoefficient_one_diagOne_and_tsum_norm_le whittakerCoefficient_unipotentGL2_mul isClosed_rationalCentreUnipotent isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant ideleNorm_det_globalPoints exists_isFundamentalDomain_globalPoints_range integral_rationalTorusUnipotentQuotient_tsum_units_eq_integral_rationalCentreUnipotentQuotient"
p2m_open "AutomorphicForm"

namespace TorusUnfoldC9C

set_option linter.deprecated false in
theorem measurable_tsum_complex {α ι : Type*} [MeasurableSpace α] [Countable ι] {f : ι → α → ℂ}
    (hf : ∀ i, Measurable (f i)) : Measurable fun x => ∑' i, f i x := by
  classical
  obtain ⟨e, he⟩ := Countable.exists_injective_nat ι
  let A : ℕ → Finset ι := fun n => (Finset.range n).preimage e (he.injOn)
  have hAmono : Monotone A := by
    intro m n hmn i hi
    simp only [A, Finset.mem_preimage, Finset.mem_range] at hi ⊢
    exact lt_of_lt_of_le hi hmn
  have hAex : ∀ i, ∃ n, i ∈ A n := fun i => ⟨e i + 1, by simp [A]⟩
  have hA : Tendsto A atTop atTop := tendsto_atTop_finset_of_monotone hAmono hAex
  let M : Set α := {x | Summable fun i => f i x}
  have key : ∀ x, (Summable fun i => f i x) ↔ (∑' i, (‖f i x‖₊ : ℝ≥0∞)) ≠ ⊤ := fun x => by
    rw [ENNReal.tsum_coe_ne_top_iff_summable, ← NNReal.summable_coe]
    simp only [coe_nnnorm]
    exact summable_norm_iff.symm
  have hM : MeasurableSet M := by
    have hmeas : Measurable fun x => ∑' i, (‖f i x‖₊ : ℝ≥0∞) :=
      Measurable.ennreal_tsum fun i => (hf i).nnnorm.coe_nnreal_ennreal
    have : M = (fun x => ∑' i, (‖f i x‖₊ : ℝ≥0∞)) ⁻¹' {⊤}ᶜ := by
      ext x
      simp only [M, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
      exact key x
    rw [this]
    exact hmeas (measurableSet_singleton ⊤).compl
  let t : ℕ → α → ℂ := fun n => M.indicator fun x => ∑ i ∈ A n, f i x
  have ht : ∀ n, Measurable (t n) := fun n => (Finset.measurable_sum _ fun i _ => hf i).indicator hM
  have hlim : ∀ x, Tendsto (fun n => t n x) atTop (𝓝 (∑' i, f i x)) := by
    intro x
    by_cases hx : x ∈ M
    · have h1 : (fun n => t n x) = (fun s : Finset ι => ∑ i ∈ s, f i x) ∘ A := by
        funext n; simp only [t, Set.indicator_of_mem hx, Function.comp_apply]
      rw [h1]
      exact (Summable.hasSum hx).comp hA
    · have h1 : (fun n => t n x) = fun _ => 0 := by
        funext n; simp only [t, Set.indicator_of_notMem hx]
      rw [h1, tsum_eq_zero_of_not_summable hx]
      exact tendsto_const_nhds
  exact measurable_of_tendsto_metrizable ht (tendsto_pi_nhds.mpr hlim)

theorem enorm_tsum_le {ι : Type*} (f : ι → ℂ) : ‖∑' i, f i‖ₑ ≤ ∑' i, ‖f i‖ₑ := by
  by_cases h : Summable f
  · have hn : Summable fun i => ‖f i‖₊ := by
      rw [← NNReal.summable_coe]; simp only [coe_nnnorm]; exact summable_norm_iff.mpr h
    calc ‖∑' i, f i‖ₑ = ((‖∑' i, f i‖₊ : ℝ≥0) : ℝ≥0∞) := rfl
      _ ≤ ((∑' i, ‖f i‖₊ : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_le_coe.mpr (nnnorm_tsum_le hn)
      _ = ∑' i, ‖f i‖ₑ := by rw [ENNReal.coe_tsum hn]; rfl
  · rw [tsum_eq_zero_of_not_summable h, enorm_zero]
    exact bot_le

variable (F : Type) [Field F] [NumberField F]

def ratCentralHom : Fˣ →* AdelicGL2 (𝓞 F) F :=
  (globalPoints (𝓞 F) F).comp (Units.map (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom)

def diagHom : Fˣ →* AdelicGL2 (𝓞 F) F :=
  (globalPoints (𝓞 F) F).comp (diagOne (A := F))

theorem ratCentralHom_apply_entry (a : Fˣ) (i j : Fin 2) :
    ((ratCentralHom F a : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j =
      if i = j then algebraMap F (AdeleRing (𝓞 F) F) a else 0 := by
  change algebraMap F (AdeleRing (𝓞 F) F) ((Matrix.scalar (Fin 2) (a : F)) i j) = _
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem diagHom_apply_entry (a : Fˣ) (i j : Fin 2) :
    ((diagHom F a : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j =
      if i = j then (if i = 0 then algebraMap F (AdeleRing (𝓞 F) F) a else 1) else 0 := by
  change algebraMap F (AdeleRing (𝓞 F) F) ((diagOne a : Matrix (Fin 2) (Fin 2) F) i j) = _
  rw [diagOne_coe_apply, Matrix.diagonal_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem ratCentralHom_comm (a : Fˣ) (g : AdelicGL2 (𝓞 F) F) : ratCentralHom F a * g = g * ratCentralHom F a := by
  refine Units.ext ?_
  change (Matrix.scalar (Fin 2) ((a : Fˣ) : F)).map (algebraMap F (AdeleRing (𝓞 F) F)) *
      (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) =
    (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) * (Matrix.scalar (Fin 2) ((a : Fˣ) : F)).map (algebraMap F (AdeleRing (𝓞 F) F))
  have : (Matrix.scalar (Fin 2) ((a : Fˣ) : F)).map (algebraMap F (AdeleRing (𝓞 F) F)) =
      Matrix.scalar (Fin 2) (algebraMap F (AdeleRing (𝓞 F) F) a) := by
    ext i j
    rw [Matrix.map_apply, Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  rw [this]
  exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq

theorem unipotentGL2_mul_diagHom (a : Fˣ) (y : AdeleRing (𝓞 F) F) :
    unipotentGL2 y * diagHom F a = diagHom F a * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ((a⁻¹ : Fˣ) : F) * y) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Matrix.mul_apply,
    Fin.sum_univ_two, Fin.sum_univ_two, diagHom_apply_entry, diagHom_apply_entry, diagHom_apply_entry,
    diagHom_apply_entry, unipotentGL2_coe]
  have hinv : algebraMap F (AdeleRing (𝓞 F) F) (a : F) * algebraMap F (AdeleRing (𝓞 F) F) ((a : F)⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel₀ a.ne_zero, map_one]
  fin_cases i <;> fin_cases j <;> simp [← mul_assoc, hinv]

theorem diagHom_mul_unipotentGL2 (a : Fˣ) (u : AdeleRing (𝓞 F) F) :
    diagHom F a * unipotentGL2 u = unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) (a : F) * u) * diagHom F a := by
  rw [unipotentGL2_mul_diagHom, ← mul_assoc, ← map_mul, Units.val_inv_eq_inv_val, inv_mul_cancel₀ a.ne_zero,
    map_one, one_mul]

theorem globalPoints_injective : Function.Injective (globalPoints (𝓞 F) F) := by
  intro x y h
  apply Units.ext
  ext i j
  have := congrArg (fun g : AdelicGL2 (𝓞 F) F => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j) h
  simp only [globalPoints_apply] at this
  exact (NumberField.AdeleRing.algebraMap_injective (R := 𝓞 F) (K := F)) this

def leftStabilizer (f : AdelicGL2 (𝓞 F) F → ℂ) : Subgroup (AdelicGL2 (𝓞 F) F) where
  carrier := {x | ∀ g, f (x * g) = f g}
  mul_mem' := by
    intro a b ha hb g
    rw [mul_assoc, ha, hb]
  one_mem' := by
    intro g
    rw [one_mul]
  inv_mem' := by
    intro a ha g
    rw [← ha (a⁻¹ * g), mul_inv_cancel_left]

abbrev scalarUnipotent : Subgroup (GL (Fin 2) F) :=
  (Units.map (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom).range ⊔ (unipotentGL2Hom (R := F)).range

abbrev ratP : Subgroup (AdelicGL2 (𝓞 F) F) :=
  rationalCentre F ⊔ ((globalPoints (𝓞 F) F).comp (unipotentGL2Hom (R := F))).range

theorem ratP_eq_map : ratP F = (scalarUnipotent F).map (globalPoints (𝓞 F) F) := by
  rw [Subgroup.map_sup, ← MonoidHom.range_comp, ← MonoidHom.range_comp]

omit [NumberField F] in
theorem scalarUnipotent_le_borel : scalarUnipotent F ≤ borelSubgroup F := by
  refine sup_le ?_ ?_
  · rintro _ ⟨a, rfl⟩
    show (Matrix.scalar (Fin 2) ((a : Fˣ) : F)) 1 0 = 0
    simp
  · rintro _ ⟨t, rfl⟩
    exact unipotentGL2_mem_borelSubgroup _

theorem ratP_le_borelMap : ratP F ≤ (borelSubgroup F).map (globalPoints (𝓞 F) F) := by
  rw [ratP_eq_map]
  exact Subgroup.map_mono (scalarUnipotent_le_borel F)

theorem diagHom_mem_borelMap (a : Fˣ) : diagHom F a ∈ (borelSubgroup F).map (globalPoints (𝓞 F) F) := by
  refine ⟨diagOne a, ?_, rfl⟩
  show (diagOne a : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  rw [diagOne_coe_apply]; simp

theorem existsUnique_repr (γ : (borelSubgroup F).map (globalPoints (𝓞 F) F)) :
    ∃! a : Fˣ, (((⟨diagHom F a, diagHom_mem_borelMap F a⟩ : (borelSubgroup F).map (globalPoints (𝓞 F) F))⁻¹ * γ :
      (borelSubgroup F).map (globalPoints (𝓞 F) F)) : AdelicGL2 (𝓞 F) F) ∈ ratP F := by
  obtain ⟨b, hb, hbγ⟩ := γ.2
  have h := existsUnique_diagOne_inv_mul_mem_scalar_sup_unipotent_of_mem_borelSubgroup F b hb
  refine (existsUnique_congr fun a => ?_).mp h
  rw [ratP_eq_map]
  have hval : (((⟨diagHom F a, diagHom_mem_borelMap F a⟩ : (borelSubgroup F).map (globalPoints (𝓞 F) F))⁻¹ * γ :
      (borelSubgroup F).map (globalPoints (𝓞 F) F)) : AdelicGL2 (𝓞 F) F) =
      globalPoints (𝓞 F) F ((diagOne a)⁻¹ * b) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, ← hbγ]
    rfl
  rw [hval, Subgroup.mem_map_iff_mem (globalPoints_injective F)]

end TorusUnfoldC9C
p2m_reactivate "P2MW.S_AutomorphicForm_peterssonIntegral_mul_bruhatEisenstein_eq_integral_whittakerCoefficient_mul_conj_rationalCentreUnipotentQuotient_of_integrable.RS11C9A"

end AutomorphicForm
p2m_reactivate "P2MW.S_AutomorphicForm_peterssonIntegral_mul_bruhatEisenstein_eq_integral_whittakerCoefficient_mul_conj_rationalCentreUnipotentQuotient_of_integrable.RS11C9A"

end
p2m_reactivate "P2MW.S_AutomorphicForm_peterssonIntegral_mul_bruhatEisenstein_eq_integral_whittakerCoefficient_mul_conj_rationalCentreUnipotentQuotient_of_integrable.RS11C9A"

noncomputable section

namespace RS11C9

open scoped Pointwise ENNReal

variable (F : Type) [Field F] [NumberField F]

scoped instance countable_numberField : Countable F :=
  (Module.finBasis ℚ F).equivFun.toEquiv.injective.countable

scoped instance countable_matrix : Countable (Matrix (Fin 2) (Fin 2) F) :=
  inferInstanceAs (Countable (Fin 2 → Fin 2 → F))

scoped instance countable_gl2 : Countable (Matrix.GeneralLinearGroup (Fin 2) F) :=
  Units.val_injective.countable

private def _root_.RS11C9.slab (d₁ d₂ : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}

p2m_export "RS11C9" "slab"
private theorem _root_.RS11C9.measurableSet_slab (d₁ d₂ : ℝ) : MeasurableSet (slab F d₁ d₂) :=
  NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc F d₁ d₂

p2m_export "RS11C9" "measurableSet_slab"
theorem globalPoints_mul_mem_slab_iff {d₁ d₂ : ℝ} (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F) :
    globalPoints (𝓞 F) F γ * g ∈ slab F d₁ d₂ ↔ g ∈ slab F d₁ d₂ := by
  simp only [slab, Set.mem_setOf_eq, map_mul, NumberField.TateGlobal.ideleNorm_mul,
    AutomorphicForm.ideleNorm_det_globalPoints, one_mul]

theorem preimage_slab {d₁ d₂ : ℝ} (γ : Matrix.GeneralLinearGroup (Fin 2) F) :
    (fun g => globalPoints (𝓞 F) F γ * g) ⁻¹' slab F d₁ d₂ = slab F d₁ d₂ := by
  ext g; exact globalPoints_mul_mem_slab_iff F γ g

theorem globalPoints_unipotentGL2 (β : F) :
    globalPoints (𝓞 F) F (unipotentGL2 β) = unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) := by
  apply Units.ext
  ext i j
  rw [globalPoints_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

private theorem _root_.RS11C9.enorm_coe_real_of_nonneg {r : ℝ} (hr : 0 ≤ r) : ‖(r : ℂ)‖ₑ = ENNReal.ofReal r := by
  rw [enorm_eq_nnnorm, Complex.nnnorm_real, ← enorm_eq_nnnorm, Real.enorm_eq_ofReal hr]

p2m_export "RS11C9" "enorm_coe_real_of_nonneg"
theorem mul_le_sq_add_sq (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with h | h
  · calc a * b ≤ b * b := mul_le_mul_left h b
      _ = b ^ 2 := (sq b).symm
      _ ≤ a ^ 2 + b ^ 2 := le_add_self
  · calc a * b ≤ a * a := mul_le_mul_right h a
      _ = a ^ 2 := (sq a).symm
      _ ≤ a ^ 2 + b ^ 2 := le_self_add

theorem ofReal_sq_norm (z : ℂ) : ENNReal.ofReal (‖z‖ ^ 2) = ‖z‖ₑ ^ 2 := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

private theorem _root_.RS11C9.indicator_comp_globalPoints_mul {β : Type*} [Zero β] {d₁ d₂ : ℝ} (γ : Matrix.GeneralLinearGroup (Fin 2) F)
    (f : AdelicGL2 (𝓞 F) F → β) (g : AdelicGL2 (𝓞 F) F) :
    (slab F d₁ d₂).indicator f (globalPoints (𝓞 F) F γ * g) =
      (slab F d₁ d₂).indicator (fun g => f (globalPoints (𝓞 F) F γ * g)) g := by
  by_cases hg : g ∈ slab F d₁ d₂
  · rw [Set.indicator_of_mem hg, Set.indicator_of_mem ((globalPoints_mul_mem_slab_iff F γ g).mpr hg)]
  · rw [Set.indicator_of_notMem hg,
      Set.indicator_of_notMem (fun h => hg ((globalPoints_mul_mem_slab_iff F γ g).mp h))]

p2m_export "RS11C9" "indicator_comp_globalPoints_mul"

private theorem _root_.RS11C9.tsum_indicator_const_set {ι β : Type*} [AddCommMonoid β] [TopologicalSpace β] (s : Set (AdelicGL2 (𝓞 F) F))
    (f : ι → AdelicGL2 (𝓞 F) F → β) (g : AdelicGL2 (𝓞 F) F) :
    ∑' i, s.indicator (f i) g = s.indicator (fun g => ∑' i, f i g) g := by
  by_cases hg : g ∈ s
  · simp only [Set.indicator_of_mem hg]
  · simp only [Set.indicator_of_notMem hg, tsum_zero]

p2m_export "RS11C9" "tsum_indicator_const_set"

theorem det_unipotentGL2 {A : Type*} [CommRing A] (u : A) : Matrix.GeneralLinearGroup.det (unipotentGL2 u) = 1 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, unipotentGL2_coe, Matrix.det_fin_two_of]
  simp

theorem unipotentGL2_mul_mem_slab_iff {d₁ d₂ : ℝ} (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F) :
    unipotentGL2 u * g ∈ slab F d₁ d₂ ↔ g ∈ slab F d₁ d₂ := by
  simp only [slab, Set.mem_setOf_eq, map_mul, det_unipotentGL2, one_mul]

theorem globalPoints_scalar_mul_comm (a : Fˣ) (g : AdelicGL2 (𝓞 F) F) :
    globalPoints (𝓞 F) F (Units.map (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom a) * g =
      g * globalPoints (𝓞 F) F (Units.map (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom a) := by
  apply Units.ext
  push_cast
  have hval : ((globalPoints (𝓞 F) F (Units.map (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom a) :
      AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) =
      Matrix.scalar (Fin 2) (algebraMap F (AdeleRing (𝓞 F) F) (a : F)) := by
    ext i j
    rw [globalPoints_apply]
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, apply_ite (algebraMap F (AdeleRing (𝓞 F) F))]
  rw [hval]
  exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq

theorem continuous_unipotentGL2 (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (fun x : A => (unipotentGL2 x : GL (Fin 2) A)) := by
  have hmat : ∀ s : A → A, Continuous s → Continuous (fun x : A => (!![1, s x; 0, 1] : Matrix (Fin 2) (Fin 2) A)) := by
    intro s hs
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp [hs, continuous_const]
  rw [Units.continuous_iff]
  constructor
  · have h__af := hmat id continuous_id
    simp [unipotentGL2_coe] at h__af
    exact h__af
  · have hinv : ∀ x : A, ((unipotentGL2 x : GL (Fin 2) A)⁻¹ : GL (Fin 2) A) = unipotentGL2 (-x) := by
      intro x
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← unipotentGL2_add, neg_add_cancel, unipotentGL2_zero]
    simp only [hinv]
    simpa [unipotentGL2_coe] using hmat Neg.neg continuous_neg

theorem diagOne_mem_borelSubgroup (a : Fˣ) : (diagOne a : Matrix.GeneralLinearGroup (Fin 2) F) ∈ borelSubgroup F := by
  rw [mem_borelSubgroup_iff]
  simp [diagOne]

theorem scalar_mem_borelSubgroup (a : Fˣ) :
    Units.map (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom a ∈ borelSubgroup F := by
  rw [mem_borelSubgroup_iff]
  simp [Matrix.scalar_apply, Matrix.diagonal_apply]

theorem ofReal_integral_le_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases hfi : Integrable f μ
  · rw [ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall hf)]
  · rw [integral_undef hfi, ENNReal.ofReal_zero]; exact bot_le

theorem sqrt_mul_sqrt_le_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : Real.sqrt a * Real.sqrt b ≤ a + b := by
  nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.sq_sqrt ha, Real.sq_sqrt hb,
    Real.sqrt_nonneg a, Real.sqrt_nonneg b]

theorem unipotentGL2_mul_globalPoints_borel (b : Matrix.GeneralLinearGroup (Fin 2) F) (hb : b ∈ borelSubgroup F)
    (u : AdeleRing (𝓞 F) F) :
    unipotentGL2 u * globalPoints (𝓞 F) F b = globalPoints (𝓞 F) F b *
      unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F)
        (((borelDiagSnd ⟨b, hb⟩ * (borelDiagFst ⟨b, hb⟩)⁻¹ : Fˣ) : F)) * u) := by
  have hb10 : (b : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hb
  have hp0 : (b : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := (borelDiagFst ⟨b, hb⟩).ne_zero
  apply Units.ext
  ext i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, unipotentGL2_coe,
    globalPoints_apply]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, borelDiagFst, borelDiagSnd, hb10]
  have hv : (b : Matrix (Fin 2) (Fin 2) F) 0 0 * ((b⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 :=
    (borelDiagFst ⟨b, hb⟩).val_inv
  rw [Matrix.coe_units_inv] at hv
  have h1 : algebraMap F (AdeleRing (𝓞 F) F) ((b : Matrix (Fin 2) (Fin 2) F) 0 0) *
      algebraMap F (AdeleRing (𝓞 F) F) ((b : Matrix (Fin 2) (Fin 2) F)⁻¹ 0 0) = 1 := by
    rw [← map_mul, hv, map_one]
  linear_combination (-(u * algebraMap F (AdeleRing (𝓞 F) F) ((b : Matrix (Fin 2) (Fin 2) F) 1 1))) * h1

end RS11C9
p2m_reactivate "P2MW.S_AutomorphicForm_peterssonIntegral_mul_bruhatEisenstein_eq_integral_whittakerCoefficient_mul_conj_rationalCentreUnipotentQuotient_of_integrable.RS11C9A P2MW.S_AutomorphicForm_peterssonIntegral_mul_bruhatEisenstein_eq_integral_whittakerCoefficient_mul_conj_rationalCentreUnipotentQuotient_of_integrable.RS11C9"

end
p2m_reactivate "P2MW.S_AutomorphicForm_peterssonIntegral_mul_bruhatEisenstein_eq_integral_whittakerCoefficient_mul_conj_rationalCentreUnipotentQuotient_of_integrable.RS11C9A P2MW.S_AutomorphicForm_peterssonIntegral_mul_bruhatEisenstein_eq_integral_whittakerCoefficient_mul_conj_rationalCentreUnipotentQuotient_of_integrable.RS11C9"

open scoped Pointwise ENNReal

open RS11C9A in
theorem unfoldB_mixed
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμF : IsIdeleClassChar (𝓞 F) F μ) (_hνF : IsIdeleClassChar (𝓞 F) F ν)
      (s : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφc : Continuous φ)
      (_hφsum : ∀ g : AdelicGL2 (𝓞 F) F, Summable fun ξ : F =>
        ‖φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖)
      (x y : AdelicGL2 (𝓞 F) F → ℂ)
      (_hxG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
        x (globalPoints (𝓞 F) F γ * g) = x g)
      (_hyG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
        y (globalPoints (𝓞 F) F γ * g) = y g)
      (_hxc : Continuous x) (_hyc : Continuous y)
      (w d₁ d₂ : ℝ) (_hd₁ : 0 < d₁) (_hd : d₁ < d₂)
      (𝓕 : Set (AdelicGL2 (𝓞 F) F))
      (_h𝓕s : 𝓕 ⊆ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
      (_h𝓕 : IsFundamentalDomain (globalPoints (𝓞 F) F).range 𝓕
        ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
          {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}))
      (_hfold : IntegrableOn (fun g => ‖x g * (starRingEnd ℂ) (y g)‖ *
          (‖φ g‖ + ∑' ξ : F, ‖φ (adelicWeyl (𝓞 F) F *
            unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖) *
          ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w)) 𝓕 (adelicGLHaar (Fin 2) (𝓞 F) F)),
    ∃ 𝓕B : Set (AdelicGL2 (𝓞 F) F), MeasurableSet 𝓕B ∧
      IsFundamentalDomain ((borelSubgroup F).map (globalPoints (𝓞 F) F)) 𝓕B (adelicGLHaar (Fin 2) (𝓞 F) F) ∧
      IntegrableOn (fun g : AdelicGL2 (𝓞 F) F =>
        ({g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}.indicator
            (fun _ => (1 : ℂ)) g) *
          (x g * φ g * (starRingEnd ℂ) (y g) *
            ((ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w) : ℝ) : ℂ))) 𝓕B (adelicGLHaar (Fin 2) (𝓞 F) F) ∧
      ∫ g in 𝓕B,
        ({g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}.indicator
            (fun _ => (1 : ℂ)) g) *
          (x g * φ g * (starRingEnd ℂ) (y g) *
            ((ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w) : ℝ) : ℂ)) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
        peterssonIntegral F w 𝓕
          (fun g => x g * (φ g + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F *
            unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g))) y := by
  intro α hα μc νc hμF hνF s φ hφ hφc hφsum x y hxG hyG hxc hyc w d₁ d₂ hd₁ hd 𝓕 h𝓕s h𝓕 hfold
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  letI := RS11C9A.ratAction F
  letI := RS11C9A.mGL F
  haveI := RS11C9A.measurableSMul_rat F

  set μG := adelicGLHaar (Fin 2) (𝓞 F) F with hμG
  have hSd : {g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂} =
      RS11C9A.slab F d₁ d₂ := rfl
  rw [hSd] at h𝓕s h𝓕 ⊢
  set Sd := RS11C9A.slab F d₁ d₂ with hSd'
  have hSdm : MeasurableSet Sd := RS11C9A.measurableSet_slab F d₁ d₂

  obtain ⟨D, hD⟩ := AutomorphicForm.exists_isFundamentalDomain_globalPoints_range F
  have hS₀ := RS11C9A.isFundamentalDomain_union_slab F h𝓕s h𝓕 hD
  obtain ⟨S, hSsub, hSm, hSeq⟩ := hS₀.nullMeasurableSet.exists_measurable_subset_ae_eq
  have hS : IsFundamentalDomain (globalPoints (𝓞 F) F).range S μG :=
    RS11C9A.isFundamentalDomain_of_ae_eq hS₀ hSeq.symm hSm.nullMeasurableSet
  have hStop := RS11C9A.isFundamentalDomain_top_of_range F hS
  have hS₀cap : (𝓕 ∪ (D \ Sd)) ∩ Sd = 𝓕 := by
    ext g; constructor
    · rintro ⟨hg | hg, hgS⟩
      · exact hg
      · exact absurd hgS hg.2
    · intro hg; exact ⟨Or.inl hg, h𝓕s hg⟩
  have hScap : (S ∩ Sd : Set _) =ᵐ[μG] 𝓕 := by
    have h := hSeq.inter (ae_eq_refl Sd)
    rwa [hS₀cap] at h

  let c : Option F → Matrix.GeneralLinearGroup (Fin 2) F :=
    fun o => o.elim 1 fun ξ => (gl2Weyl : Matrix.GeneralLinearGroup (Fin 2) F) * unipotentGL2 ξ
  let R : Option F → (⊤ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) F)) := fun o => ⟨(c o)⁻¹, trivial⟩
  have hRc : ∀ o, ((R o : Matrix.GeneralLinearGroup (Fin 2) F)⁻¹) = c o := fun o => inv_inv _
  have hR : ∀ γ : (⊤ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) F)),
      ∃! o, ((R o)⁻¹ * γ : Matrix.GeneralLinearGroup (Fin 2) F) ∈ borelSubgroup F := by
    intro γ
    have h := AutomorphicForm.existsUnique_bruhatRepresentative_mul_mem_borelSubgroup F γ
    simpa only [Subgroup.coe_inv, hRc] using h
  set 𝓕B : Set (AdelicGL2 (𝓞 F) F) := ⋃ o, ((R o : Matrix.GeneralLinearGroup (Fin 2) F)⁻¹) • S with h𝓕B
  have hFD : IsFundamentalDomain (borelSubgroup F) 𝓕B μG :=
    MeasureTheory.IsFundamentalDomain.iUnion_inv_smul_of_leftCosetRepresentatives
      μG ⊤ (borelSubgroup F) le_top S hStop R hR
  have hFDmap := RS11C9A.isFundamentalDomain_map_of F hFD
  have h𝓕Bm : MeasurableSet 𝓕B := by
    refine MeasurableSet.iUnion fun o => ?_
    rw [← Set.preimage_smul_inv]
    exact (measurable_const_smul _) hSm
  refine ⟨𝓕B, h𝓕Bm, hFDmap, ?_⟩

  set ω : AdelicGL2 (𝓞 F) F → ℝ := fun g => ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w) with hω
  have hωpos : ∀ g, 0 < ω g := fun g => Real.rpow_pos_of_pos (NumberField.TateGlobal.ideleNorm_pos _) _
  have hωc : Continuous ω :=
    (NumberField.TateGlobal.continuous_ideleNorm_det F).rpow_const fun _ =>
      Or.inl (NumberField.TateGlobal.ideleNorm_pos _).ne'
  have hωG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      ω (globalPoints (𝓞 F) F γ * g) = ω g := by
    intro γ g
    simp only [hω, map_mul, NumberField.TateGlobal.ideleNorm_mul, AutomorphicForm.ideleNorm_det_globalPoints, one_mul]
  set Ew : AdelicGL2 (𝓞 F) F → ℂ := fun g => φ g + ∑' ξ : F,
    φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g) with hEw
  set Eb : AdelicGL2 (𝓞 F) F → ℝ := fun g => ‖φ g‖ + ∑' ξ : F,
    ‖φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖ with hEb
  set Ebe : AdelicGL2 (𝓞 F) F → ℝ≥0∞ := fun g => ‖φ g‖ₑ + ∑' ξ : F,
    ‖φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖ₑ with hEbe
  have hEbe_eq : ∀ g, Ebe g = ENNReal.ofReal (Eb g) := by
    intro g
    rw [hEbe, hEb]; dsimp only
    rw [ENNReal.ofReal_add (norm_nonneg _) (tsum_nonneg fun _ => norm_nonneg _), ofReal_norm_eq_enorm,
      ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hφsum g)]
    simp only [ofReal_norm_eq_enorm]
  set Q : AdelicGL2 (𝓞 F) F → ℂ := fun g => x g * φ g * (starRingEnd ℂ) (y g) * ((ω g : ℝ) : ℂ) with hQ
  have hQc : Continuous Q :=
    ((hxc.mul hφc).mul (Complex.continuous_conj.comp hyc)).mul (Complex.continuous_ofReal.comp hωc)

  have hk₁ : (fun g : AdelicGL2 (𝓞 F) F => Sd.indicator (fun _ => (1 : ℂ)) g *
      (x g * φ g * (starRingEnd ℂ) (y g) * ((ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w) : ℝ) : ℂ))) =
      Sd.indicator Q := by
    funext g
    by_cases hg : g ∈ Sd
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg, one_mul]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, zero_mul]
  rw [hk₁]
  have hind : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (f : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F),
      Sd.indicator f (globalPoints (𝓞 F) F γ * g) = Sd.indicator (fun g => f (globalPoints (𝓞 F) F γ * g)) g :=
    fun γ f g => RS11C9A.indicator_comp_globalPoints_mul F γ f g
  have hind' : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (f : AdelicGL2 (𝓞 F) F → ℝ≥0∞) (g : AdelicGL2 (𝓞 F) F),
      Sd.indicator f (globalPoints (𝓞 F) F γ * g) = Sd.indicator (fun g => f (globalPoints (𝓞 F) F γ * g)) g :=
    fun γ f g => RS11C9A.indicator_comp_globalPoints_mul F γ f g
  have htsi : ∀ (f : Option F → AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F),
      ∑' o, Sd.indicator (f o) g = Sd.indicator (fun g => ∑' o, f o g) g :=
    fun f g => RS11C9A.tsum_indicator_const_set F Sd f g
  have htsi' : ∀ (f : Option F → AdelicGL2 (𝓞 F) F → ℝ≥0∞) (g : AdelicGL2 (𝓞 F) F),
      ∑' o, Sd.indicator (f o) g = Sd.indicator (fun g => ∑' o, f o g) g :=
    fun f g => RS11C9A.tsum_indicator_const_set F Sd f g

  have hc_none : ∀ g : AdelicGL2 (𝓞 F) F, globalPoints (𝓞 F) F (c none) * g = g := fun g => by
    show globalPoints (𝓞 F) F 1 * g = g; rw [map_one, one_mul]
  have hc_some : ∀ (ξ : F) (g : AdelicGL2 (𝓞 F) F), globalPoints (𝓞 F) F (c (some ξ)) * g =
      adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g := fun ξ g => by
    show globalPoints (𝓞 F) F ((gl2Weyl : Matrix.GeneralLinearGroup (Fin 2) F) * unipotentGL2 ξ) * g = _
    rw [RS11C9A.globalPoints_bruhat]
  have hsmul : ∀ (o : Option F) (g : AdelicGL2 (𝓞 F) F),
      ((R o : Matrix.GeneralLinearGroup (Fin 2) F)⁻¹) • g = globalPoints (𝓞 F) F (c o) * g := fun o g => by
    rw [hRc]; rfl
  have htsum_phi : ∀ g : AdelicGL2 (𝓞 F) F, ∑' o, φ (globalPoints (𝓞 F) F (c o) * g) = Ew g := by
    intro g
    have h := RS11C9A.hasSum_option (fun o => φ (globalPoints (𝓞 F) F (c o) * g)) (a := ∑' ξ : F,
      φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) (by
        simp only [hc_some]
        exact (hφsum g).of_norm.hasSum)
    rw [h.tsum_eq]
    simp only [hc_none, hEw]
  have htsum_phie : ∀ g : AdelicGL2 (𝓞 F) F, ∑' o, ‖φ (globalPoints (𝓞 F) F (c o) * g)‖ₑ = Ebe g := by
    intro g
    rw [RS11C9A.tsum_option_ennreal]
    simp only [hc_none, hc_some, hEbe]

  obtain ⟨hL, hB⟩ :=
    MeasureTheory.IsFundamentalDomain.setLIntegral_iUnion_inv_smul_eq_and_setIntegral_eq_of_leftCosetRepresentatives
      μG ⊤ (borelSubgroup F) le_top S hStop R hR

  set Gx : AdelicGL2 (𝓞 F) F → ℝ≥0∞ := fun g => ENNReal.ofReal (‖x g‖ ^ 2) * ENNReal.ofReal (ω g) * Ebe g with hGx
  set Gy : AdelicGL2 (𝓞 F) F → ℝ≥0∞ := fun g => ENNReal.ofReal (‖y g‖ ^ 2) * ENNReal.ofReal (ω g) * Ebe g with hGy
  have hmaj : ∀ (z : AdelicGL2 (𝓞 F) F → ℂ), IntegrableOn (fun g => ‖z g‖ ^ 2 * Eb g * ω g) 𝓕 μG →
      ∫⁻ g in S, Sd.indicator (fun g => ENNReal.ofReal (‖z g‖ ^ 2) * ENNReal.ofReal (ω g) * Ebe g) g ∂μG < ⊤ := by
    intro z hz
    rw [lintegral_indicator hSdm, Measure.restrict_restrict hSdm, Set.inter_comm, setLIntegral_congr hScap]
    have h2 := hz.2
    rw [HasFiniteIntegral] at h2
    refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun g => ?_)) h2
    have hEb0 : 0 ≤ Eb g := add_nonneg (norm_nonneg _) (tsum_nonneg fun _ => norm_nonneg _)
    rw [hEbe_eq, Real.enorm_eq_ofReal (mul_nonneg (mul_nonneg (sq_nonneg _) hEb0) (hωpos g).le),
      ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) hEb0), ENNReal.ofReal_mul (sq_nonneg _)]
    ring
  have hGxy_fin : ∫⁻ g in S, Sd.indicator (fun g => ‖x g‖ₑ * ‖y g‖ₑ * ENNReal.ofReal (ω g) * Ebe g) g ∂μG < ⊤ := by
    have hz : IntegrableOn (fun g => ‖x g * (starRingEnd ℂ) (y g)‖ * Eb g * ω g) 𝓕 μG := by
      simpa only [hEb] using hfold
    rw [lintegral_indicator hSdm, Measure.restrict_restrict hSdm, Set.inter_comm, setLIntegral_congr hScap]
    have h2 := hz.2
    rw [HasFiniteIntegral] at h2
    refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun g => ?_)) h2
    have hEb0 : 0 ≤ Eb g := add_nonneg (norm_nonneg _) (tsum_nonneg fun _ => norm_nonneg _)
    rw [hEbe_eq, Real.enorm_eq_ofReal (mul_nonneg (mul_nonneg (norm_nonneg _) hEb0) (hωpos g).le),
      ENNReal.ofReal_mul (mul_nonneg (norm_nonneg _) hEb0), ENNReal.ofReal_mul (norm_nonneg _),
      ofReal_norm_eq_enorm, enorm_mul, RCLike.enorm_conj]
    ring

  have hconj : ∀ (z : AdelicGL2 (𝓞 F) F → ℂ), Continuous z →
      (∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), z (globalPoints (𝓞 F) F γ * g) = z g) →
      ∫⁻ g in 𝓕B, Sd.indicator (fun g => ENNReal.ofReal (‖z g‖ ^ 2 * ‖φ g‖ * ω g)) g ∂μG =
        ∫⁻ g in S, Sd.indicator (fun g => ENNReal.ofReal (‖z g‖ ^ 2) * ENNReal.ofReal (ω g) * Ebe g) g ∂μG := by
    intro z hz hzG
    have hmeas : Measurable (Sd.indicator fun g => ENNReal.ofReal (‖z g‖ ^ 2 * ‖φ g‖ * ω g)) :=
      (ENNReal.measurable_ofReal.comp (((hz.norm.pow 2).mul hφc.norm).mul hωc).measurable).indicator hSdm
    rw [hL _ hmeas]
    refine lintegral_congr fun g => ?_
    simp only [hsmul, hind', hzG, hωG]
    rw [htsi']
    congr 1
    funext g
    rw [← htsum_phie g, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun o => ?_
    rw [ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (norm_nonneg _)), ENNReal.ofReal_mul (sq_nonneg _),
      ofReal_norm_eq_enorm]
    ring

  have hEbem : Measurable Ebe :=
    (hφc.measurable.enorm).add (Measurable.ennreal_tsum fun ξ =>
      (hφc.comp (continuous_const.mul continuous_id)).measurable.enorm)
  have hGm : ∀ (z : AdelicGL2 (𝓞 F) F → ℂ), Continuous z →
      Measurable (Sd.indicator fun g => ENNReal.ofReal (‖z g‖ ^ 2) * ENNReal.ofReal (ω g) * Ebe g) := fun z hz =>
    (((ENNReal.measurable_ofReal.comp (hz.norm.pow 2).measurable).mul
      (ENNReal.measurable_ofReal.comp hωc.measurable)).mul hEbem).indicator hSdm

  have hfin : ∫⁻ g in S, ∑' o, ‖(Sd.indicator Q) (((R o : Matrix.GeneralLinearGroup (Fin 2) F)⁻¹) • g)‖ₑ ∂μG < ∞ := by
    have hpt : ∀ g : AdelicGL2 (𝓞 F) F, ∑' o, ‖(Sd.indicator Q) (((R o : Matrix.GeneralLinearGroup (Fin 2) F)⁻¹) • g)‖ₑ ≤
        Sd.indicator (fun g => ‖x g‖ₑ * ‖y g‖ₑ * ENNReal.ofReal (ω g) * Ebe g) g := by
      intro g
      simp only [hsmul, enorm_indicator_eq_indicator_enorm, hind']
      rw [htsi']
      by_cases hg : g ∈ Sd
      swap
      · simp only [Set.indicator_of_notMem hg]; exact le_rfl
      simp only [Set.indicator_of_mem hg]
      have hterm : ∀ o, ‖Q (globalPoints (𝓞 F) F (c o) * g)‖ₑ =
          ‖x g‖ₑ * ‖y g‖ₑ * ENNReal.ofReal (ω g) * ‖φ (globalPoints (𝓞 F) F (c o) * g)‖ₑ := by
        intro o
        simp only [hQ, hxG, hyG, hωG, enorm_mul, RCLike.enorm_conj, RS11C9A.enorm_coe_real_of_nonneg (hωpos g).le]
        ring
      simp only [hterm]
      rw [ENNReal.tsum_mul_left, htsum_phie]
    calc ∫⁻ g in S, ∑' o, ‖(Sd.indicator Q) (((R o : Matrix.GeneralLinearGroup (Fin 2) F)⁻¹) • g)‖ₑ ∂μG
        ≤ ∫⁻ g in S, Sd.indicator (fun g => ‖x g‖ₑ * ‖y g‖ₑ * ENNReal.ofReal (ω g) * Ebe g) g ∂μG := lintegral_mono hpt
      _ < ⊤ := hGxy_fin
  obtain ⟨hint, -, hid⟩ := hB (Sd.indicator Q) ((hQc.aestronglyMeasurable).indicator hSdm) hfin
  refine ⟨hint, ?_⟩
  ·
    rw [hid]

    set P : AdelicGL2 (𝓞 F) F → ℂ := fun g => x g * Ew g * (starRingEnd ℂ) (y g) * ((ω g : ℝ) : ℂ) with hP
    have hsumQ : ∀ g : AdelicGL2 (𝓞 F) F,
        ∑' o, (Sd.indicator Q) (((R o : Matrix.GeneralLinearGroup (Fin 2) F)⁻¹) • g) = Sd.indicator P g := by
      intro g
      simp only [hsmul, hind]
      rw [htsi]
      congr 1
      funext g
      have hterm : ∀ o, Q (globalPoints (𝓞 F) F (c o) * g) =
          (x g * (starRingEnd ℂ) (y g) * ((ω g : ℝ) : ℂ)) * φ (globalPoints (𝓞 F) F (c o) * g) := by
        intro o; simp only [hQ, hxG, hyG, hωG]; ring
      simp only [hterm]
      rw [tsum_mul_left, htsum_phi, hP]
      ring
    simp_rw [hsumQ]
    rw [setIntegral_indicator hSdm, setIntegral_congr_set hScap]
    rfl

open RS11C9 in
theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
      (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
      (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (_hψ : IsGlobalAddChar F ψ)
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμF : IsIdeleClassChar (𝓞 F) F μ) (_hνF : IsIdeleClassChar (𝓞 F) F ν)
      (s : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφc : Continuous φ)
      (_hφsum : ∀ g : AdelicGL2 (𝓞 F) F, Summable fun ξ : F =>
        ‖φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖)
      (x y : AdelicGL2 (𝓞 F) F → ℂ)
      (_hxG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
        x (globalPoints (𝓞 F) F γ * g) = x g)
      (_hyG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
        y (globalPoints (𝓞 F) F γ * g) = y g)
      (_hxc : Continuous x) (_hyc : Continuous y)
      (_hx0 : ∀ g, whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ x 0 g = 0)
      (_hxW : ∀ g, Summable fun a : F =>
        ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ x a g‖)
      (w d₁ d₂ : ℝ) (_hd₁ : 0 < d₁) (_hd : d₁ < d₂)
      (𝓕 : Set (AdelicGL2 (𝓞 F) F))
      (_h𝓕s : 𝓕 ⊆ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
      (_h𝓕 : IsFundamentalDomain (globalPoints (𝓞 F) F).range 𝓕
        ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
          {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}))
      (_hfold : IntegrableOn (fun g => ‖x g * (starRingEnd ℂ) (y g)‖ *
          (‖φ g‖ + ∑' ξ : F, ‖φ (adelicWeyl (𝓞 F) F *
            unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖) *
          ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w)) 𝓕 (adelicGLHaar (Fin 2) (𝓞 F) F))
      (_hunf :
        Integrable (fun q : RationalCentreUnipotentQuotient F =>
            ({g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}.indicator
                (fun _ => (1 : ℂ)) q.out) *
              whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ x 1 q.out *
              (starRingEnd ℂ) (whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ y 1 q.out) *
              φ q.out *
              ((ideleNorm F (Matrix.GeneralLinearGroup.det q.out) ^ (-w) : ℝ) : ℂ))
            (rationalCentreUnipotentQuotientMeasure F)),
    peterssonIntegral F w 𝓕
        (fun g => x g * (φ g + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F *
          unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g))) y =
      ∫ q : RationalCentreUnipotentQuotient F,
        ({g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}.indicator
            (fun _ => (1 : ℂ)) q.out) *
          whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ x 1 q.out *
          (starRingEnd ℂ) (whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ y 1 q.out) *
          φ q.out *
          ((ideleNorm F (Matrix.GeneralLinearGroup.det q.out) ^ (-w) : ℝ) : ℂ)
        ∂(rationalCentreUnipotentQuotientMeasure F) := by
  intro α hα D U gen ψ hψ μc νc hμu hνu hμF hνF s φ hφ hφc hφsum x y hxG hyG hxc hyc hx0 hxW w d₁ d₂ hd₁ hd 𝓕 h𝓕s h𝓕
    hfold hunf
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 F) F) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F) := NumberField.AdeleRing.secondCountableTopology F
  set μG := adelicGLHaar (Fin 2) (𝓞 F) F with hμG
  haveI : SigmaCompactSpace (AdelicGL2 (𝓞 F) F) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite μG := Measure.IsHaarMeasure.sigmaFinite μG
  haveI : SFinite μG := instSFiniteOfSigmaFinite
  have hSd : {g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂} =
      RS11C9.slab F d₁ d₂ := rfl

  obtain ⟨𝓕B, h𝓕Bm, hFD, hint₁, hid₁⟩ :=
    unfoldB_mixed F hα μc νc
      hμF hνF s φ hφ hφc hφsum x y hxG hyG hxc hyc w d₁ d₂ hd₁ hd 𝓕 h𝓕s h𝓕 hfold
  rw [← hid₁]
  simp only [hSd] at h𝓕s h𝓕 hfold hunf hint₁ ⊢
  set Sd := RS11C9.slab F d₁ d₂ with hSd'
  have hSdm : MeasurableSet Sd := RS11C9.measurableSet_slab F d₁ d₂

  have hH₂c := AutomorphicForm.isClosed_rationalTorusUnipotent F
  obtain ⟨hH₂haar, hH₂right⟩ := AutomorphicForm.isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant F
  have hHc := AutomorphicForm.isClosed_rationalCentreUnipotent F
  obtain ⟨hHhaar, hHright⟩ := AutomorphicForm.isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant F
  have h42 := AutomorphicForm.isFundamentalDomain_boxSheet_rationalTorusUnipotent F
  dsimp only at h42
  obtain ⟨hBle, hBcount, hT₂m, hT₂FD, hT₂int⟩ := h42
  haveI : Countable ((borelSubgroup F).map (globalPoints (𝓞 F) F)) := hBcount

  set ω : AdelicGL2 (𝓞 F) F → ℝ := fun g => ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w) with hω
  have hωpos : ∀ g, 0 < ω g := fun g => Real.rpow_pos_of_pos (NumberField.TateGlobal.ideleNorm_pos _) _
  have hωc : Continuous ω :=
    (NumberField.TateGlobal.continuous_ideleNorm_det F).rpow_const fun _ =>
      Or.inl (NumberField.TateGlobal.ideleNorm_pos _).ne'
  have hωG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      ω (globalPoints (𝓞 F) F γ * g) = ω g := fun γ g => by
    simp only [hω, map_mul, NumberField.TateGlobal.ideleNorm_mul, AutomorphicForm.ideleNorm_det_globalPoints, one_mul]
  have hωN : ∀ (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F), ω (unipotentGL2 u * g) = ω g := fun u g => by
    simp only [hω, map_mul, RS11C9.det_unipotentGL2, one_mul]
  obtain ⟨hφB, hφN⟩ :=
    AutomorphicForm.IsInducedSection.apply_globalPoints_mul_of_mem_borelSubgroup_and_apply_unipotentGL2_mul F hα μc νc
      hμF hνF s φ hφ
  have hindG : ∀ {β : Type} [Zero β] (γ : Matrix.GeneralLinearGroup (Fin 2) F) (f : AdelicGL2 (𝓞 F) F → β) (g : AdelicGL2 (𝓞 F) F),
      Sd.indicator f (globalPoints (𝓞 F) F γ * g) = Sd.indicator (fun g => f (globalPoints (𝓞 F) F γ * g)) g :=
    fun γ f g => RS11C9.indicator_comp_globalPoints_mul F γ f g
  have hindN : ∀ {β : Type} [Zero β] (u : AdeleRing (𝓞 F) F) (f : AdelicGL2 (𝓞 F) F → β) (g : AdelicGL2 (𝓞 F) F),
      Sd.indicator f (unipotentGL2 u * g) = Sd.indicator (fun g => f (unipotentGL2 u * g)) g := by
    intro β _ u f g
    by_cases hg : g ∈ Sd
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem ((RS11C9.unipotentGL2_mul_mem_slab_iff F u g).mpr hg)]
    · rw [Set.indicator_of_notMem hg,
        Set.indicator_of_notMem (fun h => hg ((RS11C9.unipotentGL2_mul_mem_slab_iff F u g).mp h))]

  set Wx : AdelicGL2 (𝓞 F) F → ℂ := fun g =>
    whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ x 1 g with hWx
  set Wy : AdelicGL2 (𝓞 F) F → ℂ := fun g =>
    whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ y 1 g with hWy

  set k₃ : AdelicGL2 (𝓞 F) F → ℂ := fun g => Sd.indicator (fun _ => (1 : ℂ)) g * Wx g * (starRingEnd ℂ) (Wy g) *
    φ g * ((ω g : ℝ) : ℂ) with hk₃

  have hψc : Continuous ψ := hψ.continuous
  have hWdef : ∀ (z : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F),
      whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ z 1 g =
        ∫ u, z (unipotentGL2 u * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) 1 * u))
          ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) := by
    intro z g; rfl
  have hWmeas : ∀ (z : AdelicGL2 (𝓞 F) F → ℂ), Continuous z →
      Measurable fun g => whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ z 1 g := by
    intro z hz
    simp only [hWdef]
    have hsm : StronglyMeasurable (Function.uncurry fun (g : AdelicGL2 (𝓞 F) F) (u : AdeleRing (𝓞 F) F) =>
        z (unipotentGL2 u * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) 1 * u))) := by
      refine Continuous.stronglyMeasurable ?_
      exact (hz.comp (((RS11C9.continuous_unipotentGL2 _).comp continuous_snd).mul continuous_fst)).mul
        (hψc.comp ((continuous_const.mul continuous_snd).neg))
    exact (hsm.integral_prod_right' (ν := ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))).measurable

  have hWZ : ∀ (z : AdelicGL2 (𝓞 F) F → ℂ), (∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) g, z (globalPoints (𝓞 F) F γ * g) = z g) →
      ∀ (a : Fˣ) (g : AdelicGL2 (𝓞 F) F),
      whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ z 1
        (globalPoints (𝓞 F) F (Units.map (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom a) * g) =
      whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ z 1 g := by
    intro z hzG a g
    simp only [hWdef]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    show z (unipotentGL2 u * (_ * g)) * _ = z (unipotentGL2 u * g) * _
    rw [← mul_assoc, ← RS11C9.globalPoints_scalar_mul_comm F a (unipotentGL2 u), mul_assoc, hzG]

  have hWN : ∀ (z : AdelicGL2 (𝓞 F) F → ℂ), (∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) g, z (globalPoints (𝓞 F) F γ * g) = z g) →
      ∀ (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F),
      whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ z 1 (unipotentGL2 u * g) =
        ψ u * whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ z 1 g := by
    intro z hzG u g
    have hper : ∀ (β : F) (v : AdeleRing (𝓞 F) F),
        z (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β + v) * g) = z (unipotentGL2 v * g) := by
      intro β v
      rw [unipotentGL2_add, ← RS11C9.globalPoints_unipotentGL2, mul_assoc, hzG]
    have h := AutomorphicForm.whittakerCoefficient_unipotentGL2_mul F D U gen ψ hψ.principalInvariant z g hper 1 u
    rw [h, map_one, one_mul]
  have hψnorm : ∀ u : AdeleRing (𝓞 F) F, ‖ψ u‖ = 1 :=
    NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar F hψ
  have hψconj : ∀ u : AdeleRing (𝓞 F) F, ψ u * (starRingEnd ℂ) (ψ u) = 1 := fun u => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hψnorm, one_pow]; simp

  have hk₃Z : ∀ (a : Fˣ) (g : AdelicGL2 (𝓞 F) F),
      k₃ (globalPoints (𝓞 F) F (Units.map (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom a) * g) = k₃ g := by
    intro a g
    simp only [hk₃, hWx, hWy, hWZ x hxG, hWZ y hyG, hωG, hφB _ (RS11C9.scalar_mem_borelSubgroup F a)]
    rw [hindG]
  have hk₃N : ∀ (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F), k₃ (unipotentGL2 u * g) = k₃ g := by
    intro u g
    simp only [hk₃, hWx, hWy, hWN x hxG, hWN y hyG, hωN, hφN]
    rw [hindN, map_mul]
    calc Sd.indicator (fun _ => (1 : ℂ)) g * (ψ u * whittakerCoefficient F _ ψ x 1 g) *
          ((starRingEnd ℂ) (ψ u) * (starRingEnd ℂ) (whittakerCoefficient F _ ψ y 1 g)) * φ g * ((ω g : ℝ) : ℂ)
        = (ψ u * (starRingEnd ℂ) (ψ u)) * (Sd.indicator (fun _ => (1 : ℂ)) g * whittakerCoefficient F _ ψ x 1 g *
            (starRingEnd ℂ) (whittakerCoefficient F _ ψ y 1 g) * φ g * ((ω g : ℝ) : ℂ)) := by ring
      _ = _ := by rw [hψconj, one_mul]
  have hk₃H : ∀ h ∈ rationalCentreUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, k₃ (h * g) = k₃ g := by
    intro h hh0
    have hh : h ∈ rationalCentre F ⊔ adelicUnipotent F := hh0
    rw [Subgroup.sup_eq_closure] at hh
    refine Subgroup.closure_induction (p := fun h _ => ∀ g : AdelicGL2 (𝓞 F) F, k₃ (h * g) = k₃ g) ?_ ?_ ?_ ?_ hh
    · rintro z (⟨a, rfl⟩ | ⟨u, rfl⟩) g
      · exact hk₃Z a g
      · exact hk₃N u.toAdd g
    · intro g; rw [one_mul]
    · intro a b _ _ ha hb g; rw [mul_assoc, ha, hb]
    · intro a _ ha g
      have := ha (a⁻¹ * g)
      rw [← mul_assoc, mul_inv_cancel, one_mul] at this
      exact this.symm

  have hk₃m : Measurable k₃ := by
    simp only [hk₃]
    refine ((((measurable_const.indicator hSdm).mul (hWmeas x hxc)).mul
      (Complex.continuous_conj.measurable.comp (hWmeas y hyc))).mul hφc.measurable).mul
      (Complex.continuous_ofReal.measurable.comp hωc.measurable)

  set ν₀ : Measure (AdeleRing (𝓞 F) F) := ((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹ • adelicAddHaar (𝓞 F) F with hν₀
  have hleNU : adelicUnipotent F ≤ rationalTorus F ⊔ adelicUnipotent F := le_sup_right
  set ι₂ : AdeleRing (𝓞 F) F → rationalTorusUnipotent F := fun u =>
    Subgroup.inclusion hleNU (toAdelicUnipotent F u) with hι₂
  have hι₂c : Continuous ι₂ := by
    refine continuous_induced_rng.2 ?_
    show Continuous fun u : AdeleRing (𝓞 F) F => ((Subgroup.inclusion hleNU (toAdelicUnipotent F u) : rationalTorusUnipotent F) :
      AdelicGL2 (𝓞 F) F)
    exact RS11C9.continuous_unipotentGL2 _
  have hι₂m : Measurable ι₂ := hι₂c.measurable
  have hcoeι : ∀ u : AdeleRing (𝓞 F) F, ((ι₂ u : rationalTorusUnipotent F) : AdelicGL2 (𝓞 F) F) = unipotentGL2 u :=
    fun u => rfl
  have M2 : (rationalTorusUnipotentHaar F).restrict (ι₂ '' adelicBox F) = Measure.map ι₂ (ν₀.restrict (adelicBox F)) := by
    refine Measure.ext fun A hA => ?_
    rw [Measure.map_apply hι₂m hA, Measure.restrict_apply (hι₂m hA), ← lintegral_indicator_one hA,
      hT₂int (A.indicator 1) (measurable_one.indicator hA), ← lintegral_indicator_one ((hι₂m hA).inter (measurableSet_adelicBox F)),
      ← lintegral_indicator (measurableSet_adelicBox F)]
    refine lintegral_congr fun u => ?_
    change (adelicBox F).indicator (fun u => A.indicator (1 : rationalTorusUnipotent F → ℝ≥0∞) (ι₂ u)) u =
      (ι₂ ⁻¹' A ∩ adelicBox F).indicator 1 u
    by_cases h1 : u ∈ adelicBox F <;> by_cases h2 : ι₂ u ∈ A <;>
      simp [Set.indicator_apply, Set.mem_preimage, h1, h2]
  have hν : ν₀.restrict (adelicBox F) = (productionPinsOf F D U gen (adelicBox F)).ν := by
    show (((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹ • adelicAddHaar (𝓞 F) F).restrict (adelicBox F) =
      ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)
    rw [ProbabilityTheory.cond, Measure.restrict_smul]

  have hν₀box : ν₀ (adelicBox F) = 1 := by
    rw [hν₀, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (adelicAddHaar_adelicBox_pos F).ne' (adelicAddHaar_adelicBox_lt_top F).ne
  haveI : IsProbabilityMeasure (ν₀.restrict (adelicBox F)) := by
    rw [hν]; exact NumberField.AdelicBox.isProbabilityMeasure_cond_adelicBox F

  obtain ⟨hPle, hPcount, hT₁m, hT₁fd, hT₁int⟩ := AutomorphicForm.isFundamentalDomain_boxSheet_rationalCentreUnipotent F
  haveI : Countable (AutomorphicForm.TorusUnfoldC9C.ratP F) := hPcount
  haveI : Countable Fˣ := Function.Injective.countable (f := (Units.val : Fˣ → F)) Units.val_injective
  haveI : SMulInvariantMeasure (AdelicGL2 (𝓞 F) F) (AdelicGL2 (𝓞 F) F) μG :=
    Measure.IsMulLeftInvariant.smulInvariantMeasure
  haveI := hHhaar
  haveI := hHright
  set Rτ : Fˣ → ((borelSubgroup F).map (globalPoints (𝓞 F) F)) := fun a =>
    ⟨AutomorphicForm.TorusUnfoldC9C.diagHom F a, AutomorphicForm.TorusUnfoldC9C.diagHom_mem_borelMap F a⟩ with hRτ_def
  have hRτ : ∀ γ : ((borelSubgroup F).map (globalPoints (𝓞 F) F)), ∃! a : Fˣ,
      (((Rτ a)⁻¹ * γ : ((borelSubgroup F).map (globalPoints (𝓞 F) F))) : AdelicGL2 (𝓞 F) F) ∈
        AutomorphicForm.TorusUnfoldC9C.ratP F :=
    AutomorphicForm.TorusUnfoldC9C.existsUnique_repr F
  have hFD₂ : IsFundamentalDomain (AutomorphicForm.TorusUnfoldC9C.ratP F)
      (⋃ a : Fˣ, ((Rτ a : AdelicGL2 (𝓞 F) F)⁻¹) • 𝓕B) μG :=
    MeasureTheory.IsFundamentalDomain.iUnion_inv_smul_of_leftCosetRepresentatives μG
      ((borelSubgroup F).map (globalPoints (𝓞 F) F)) (AutomorphicForm.TorusUnfoldC9C.ratP F)
      (AutomorphicForm.TorusUnfoldC9C.ratP_le_borelMap F) 𝓕B hFD Rτ hRτ
  obtain ⟨hC1l, hC1b⟩ :=
    MeasureTheory.IsFundamentalDomain.setLIntegral_iUnion_inv_smul_eq_and_setIntegral_eq_of_leftCosetRepresentatives μG
      ((borelSubgroup F).map (globalPoints (𝓞 F) F)) (AutomorphicForm.TorusUnfoldC9C.ratP F)
      (AutomorphicForm.TorusUnfoldC9C.ratP_le_borelMap F) 𝓕B hFD Rτ hRτ
  have _hpin := fun (hk : AEStronglyMeasurable k₃ μG) => hC1b k₃ hk
  have hRτinv : ∀ (a : Fˣ) (g : AdelicGL2 (𝓞 F) F), ((Rτ a : AdelicGL2 (𝓞 F) F))⁻¹ • g =
      AutomorphicForm.TorusUnfoldC9C.diagHom F a⁻¹ * g := by
    intro a g
    rw [smul_eq_mul, hRτ_def]
    simp only [map_inv]
  have hδ : ∀ a : Fˣ, globalPoints (𝓞 F) F (diagOne a) = AutomorphicForm.TorusUnfoldC9C.diagHom F a := fun a => rfl
  have hreidx_e : ∀ g : AdelicGL2 (𝓞 F) F,
      (∑' a : Fˣ, ‖k₃ (((Rτ a : AdelicGL2 (𝓞 F) F))⁻¹ • g)‖ₑ) = ∑' a : Fˣ, ‖k₃ (globalPoints (𝓞 F) F (diagOne a) * g)‖ₑ := by
    intro g
    simp_rw [hRτinv, hδ]
    exact (Equiv.inv Fˣ).tsum_eq (fun a => ‖k₃ (AutomorphicForm.TorusUnfoldC9C.diagHom F a * g)‖ₑ)
  have hk₃P : ∀ γ ∈ AutomorphicForm.TorusUnfoldC9C.ratP F, ∀ g : AdelicGL2 (𝓞 F) F, ‖k₃ (γ * g)‖ₑ = ‖k₃ g‖ₑ :=
    fun γ hγ g => by rw [hk₃H γ (hPle hγ) g]
  have hmass₁ : rationalCentreUnipotentHaar F
      ((fun u : AdeleRing (𝓞 F) F => Subgroup.inclusion le_sup_right (toAdelicUnipotent F u)) '' adelicBox F) = 1 := by
    have h := hT₁int (fun _ => 1) measurable_const
    rw [setLIntegral_one, setLIntegral_one, Measure.smul_apply, smul_eq_mul,
      ENNReal.inv_mul_cancel (adelicAddHaar_adelicBox_pos F).ne' (adelicAddHaar_adelicBox_lt_top F).ne] at h
    exact h
  have hunf' : Integrable (fun q : RationalCentreUnipotentQuotient F => k₃ q.out)
      (rationalCentreUnipotentQuotientMeasure F) := by
    simpa only [hk₃] using hunf
  have hfin₃ : ∫⁻ g in 𝓕B, ∑' a : Fˣ, ‖k₃ (globalPoints (𝓞 F) F (diagOne a) * g)‖ₑ ∂μG < ∞ := by
    have h1 : ∫⁻ g in 𝓕B, ∑' a : Fˣ, ‖k₃ (globalPoints (𝓞 F) F (diagOne a) * g)‖ₑ ∂μG =
        ∫⁻ g in ⋃ a : Fˣ, ((Rτ a : AdelicGL2 (𝓞 F) F)⁻¹) • 𝓕B, ‖k₃ g‖ₑ ∂μG := by
      rw [hC1l _ hk₃m.enorm]
      simp_rw [hreidx_e]
    rw [h1, HaarQuotient.setLIntegral_eq_lintegral_setLIntegral_mul_out μG (rationalCentreUnipotent F) hHc
      (rationalCentreUnipotentHaar F) (AutomorphicForm.TorusUnfoldC9C.ratP F) hPle (fun g => ‖k₃ g‖ₑ) hk₃m.enorm
      hk₃P _ hFD₂ _ hT₁fd]
    have hfib : ∀ q : RationalCentreUnipotentQuotient F,
        (∫⁻ x in (fun u : AdeleRing (𝓞 F) F => Subgroup.inclusion le_sup_right (toAdelicUnipotent F u)) '' adelicBox F,
          ‖k₃ ((x : AdelicGL2 (𝓞 F) F) * q.out)‖ₑ ∂(rationalCentreUnipotentHaar F)) = ‖k₃ q.out‖ₑ := by
      intro q
      have : (fun x : rationalCentreUnipotent F => ‖k₃ ((x : AdelicGL2 (𝓞 F) F) * q.out)‖ₑ) = fun _ => ‖k₃ q.out‖ₑ :=
        funext fun x => by rw [hk₃H x x.2]
      rw [this, setLIntegral_const, hmass₁, mul_one]
    have h2 := hunf'.2
    rw [HasFiniteIntegral] at h2
    refine lt_of_le_of_lt (le_of_eq ?_) h2
    exact lintegral_congr fun q => hfib q

  obtain ⟨-, -, hC, hD'⟩ :=
    AutomorphicForm.integral_rationalTorusUnipotentQuotient_tsum_units_eq_integral_rationalCentreUnipotentQuotient F 𝓕B hFD
      k₃ hk₃m hk₃H hfin₃

  set k₁ : AdelicGL2 (𝓞 F) F → ℂ := fun g => Sd.indicator (fun _ => (1 : ℂ)) g *
    (x g * φ g * (starRingEnd ℂ) (y g) * ((ω g : ℝ) : ℂ)) with hk₁
  have hk₁m : Measurable k₁ :=
    (measurable_const.indicator hSdm).mul ((((hxc.mul hφc).mul (Complex.continuous_conj.comp hyc)).mul
      (Complex.continuous_ofReal.comp hωc)).measurable)
  have hk₁B : ∀ γ ∈ (borelSubgroup F).map (globalPoints (𝓞 F) F), ∀ g : AdelicGL2 (𝓞 F) F, k₁ (γ * g) = k₁ g := by
    rintro _ ⟨b, hb, rfl⟩ g
    simp only [hk₁, hxG, hyG, hωG, hφB b hb]
    rw [hindG]
  have hfin₁ : ∫⁻ g in 𝓕B, ‖k₁ g‖ₑ ∂μG < ∞ := hint₁.2
  obtain ⟨-, -, hC2⟩ :=
    HaarQuotient.integrable_setIntegral_mul_out_and_setIntegral_eq_integral_setIntegral_mul_out μG
      (rationalTorusUnipotent F) hH₂c (rationalTorusUnipotentHaar F) ((borelSubgroup F).map (globalPoints (𝓞 F) F))
      hBle k₁ hk₁m hk₁B 𝓕B hFD _ hT₂FD hfin₁
  show ∫ g in 𝓕B, k₁ g ∂μG = _
  rw [hC2, ← hD', ← hC]

  have hPars := fun g => (AutomorphicForm.integral_mul_conj_unipotent_eq_tsum_units_whittakerCoefficient_one_diagOne_and_tsum_norm_le
    F D U gen ψ hψ x y hxG hyG hxc hyc hx0 hxW g).2.2
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)

  show ∫ t in ι₂ '' adelicBox F, k₁ ((t : AdelicGL2 (𝓞 F) F) * q.out) ∂(rationalTorusUnipotentHaar F) =
    ∑' a : Fˣ, k₃ (globalPoints (𝓞 F) F (diagOne a) * q.out)
  have hkm : AEStronglyMeasurable (fun t : rationalTorusUnipotent F => k₁ ((t : AdelicGL2 (𝓞 F) F) * q.out))
      (Measure.map ι₂ (ν₀.restrict (adelicBox F))) :=
    (hk₁m.comp (continuous_subtype_val.mul continuous_const).measurable).aestronglyMeasurable
  rw [show (∫ t in ι₂ '' adelicBox F, k₁ ((t : AdelicGL2 (𝓞 F) F) * q.out) ∂(rationalTorusUnipotentHaar F)) =
      ∫ t, k₁ ((t : AdelicGL2 (𝓞 F) F) * q.out) ∂((rationalTorusUnipotentHaar F).restrict (ι₂ '' adelicBox F)) from rfl,
    M2, integral_map hι₂m.aemeasurable hkm]
  simp only [hcoeι]
  have hk₁N : ∀ (u : AdeleRing (𝓞 F) F) (g₀ : AdelicGL2 (𝓞 F) F), k₁ (unipotentGL2 u * g₀) =
      (Sd.indicator (fun _ => (1 : ℂ)) g₀ * φ g₀ * ((ω g₀ : ℝ) : ℂ)) *
        (x (unipotentGL2 u * g₀) * (starRingEnd ℂ) (y (unipotentGL2 u * g₀))) := by
    intro u g₀
    simp only [hk₁, hφN, hωN]
    rw [hindN]
    ring
  simp only [hk₁N]
  have hP' : ∫ u, x (unipotentGL2 u * q.out) * (starRingEnd ℂ) (y (unipotentGL2 u * q.out)) ∂(ν₀.restrict (adelicBox F)) =
      ∑' a : Fˣ, whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ x 1 (globalPoints (𝓞 F) F (diagOne a) * q.out) *
        (starRingEnd ℂ) (whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ y 1
          (globalPoints (𝓞 F) F (diagOne a) * q.out)) := by
    rw [hν]; exact hPars q.out
  rw [integral_const_mul, hP', ← tsum_mul_left]
  refine tsum_congr fun a => ?_
  simp only [hk₃, hWx, hWy, hωG, hφB _ (RS11C9.diagOne_mem_borelSubgroup F a)]
  rw [hindG]
  ring

end S_AutomorphicForm_peterssonIntegral_mul_bruhatEisenstein_eq_integral_whittakerCoefficient_mul_conj_rationalCentreUnipotentQuotient_of_integrable
end P2MW
export P2MW.S_AutomorphicForm_peterssonIntegral_mul_bruhatEisenstein_eq_integral_whittakerCoefficient_mul_conj_rationalCentreUnipotentQuotient_of_integrable (solution)
