-- Prove2me | solution 1 for AutomorphicForm.exists_continuous_forall_principalIdeles_eLpNorm_sub_lt_of_memLp_withDensity_ideleNorm_inv_prod_maximalCompactHaar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/804b0b2c-62c5-5d06-8686-b607ef6da1ec

import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_CarrierPins
import Mathlib
import Theorems.Thm_NumberField_Idele_t2Space_and_secondCountable_and_locallyCompact_and_exists_isHaarMeasure_map_mk_restrict_of_isFundamentalDomain
import Theorems.Thm_NumberField_AdeleRing_polishSpace_units
import Theorems.Thm_NumberField_AdeleRing_exists_isOpen_inter_principalIdeles_eq_singleton
import Theorems.Thm_NumberField_Idele_aestronglyMeasurable_of_continuous_prod_maximalCompact
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_continuous_forall_principalIdeles_eLpNorm_sub_lt_of_memLp_withDensity_ideleNorm_inv_prod_maximalCompactHaar
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm
open scoped NNReal ENNReal Topology Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

attribute [local instance] NumberField.Idele.isHaarMeasure_idelicHaar

noncomputable section

namespace Ws31
namespace S1a

open NumberField.TateGlobal

variable (F : Type) [Field F] [NumberField F]

abbrev I : Type := (AdeleRing (𝓞 F) F)ˣ

abbrev Pr : Subgroup (I F) := M4aHerbrand.principalIdeles (𝓞 F) F

abbrev C : Type := I F ⧸ Pr F

abbrev KK : Type := ↥(adelicMaximalCompact F)

scoped instance polish_I : PolishSpace (I F) := NumberField.AdeleRing.polishSpace_units F

scoped instance secondCountable_K : SecondCountableTopology (KK F) := by
  haveI := NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  exact TopologicalSpace.Subtype.secondCountableTopology _

scoped instance polish_K : PolishSpace (KK F) := by
  letI : MetricSpace (KK F) := TopologicalSpace.metrizableSpaceMetric (KK F)
  haveI : CompleteSpace (KK F) := complete_of_compact
  infer_instance

scoped instance discrete_Pr : DiscreteTopology ↥(Pr F) := by
  obtain ⟨V, hV, hVP⟩ := NumberField.AdeleRing.exists_isOpen_inter_principalIdeles_eq_singleton F
  refine discreteTopology_of_isOpen_singleton_one ?_
  have : ({1} : Set ↥(Pr F)) = Subtype.val ⁻¹' V := by
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · rintro rfl
      have h1 : (1 : I F) ∈ V ∩ (Pr F : Set (I F)) := by rw [hVP]; rfl
      exact h1.1
    · intro hx
      have h1 : (x : I F) ∈ V ∩ (Pr F : Set (I F)) := ⟨hx, x.2⟩
      rw [hVP] at h1
      exact Subtype.ext h1
  rw [this]
  exact hV.preimage continuous_subtype_val

scoped instance closed_Pr : IsClosed ((Pr F : Subgroup (I F)) : Set (I F)) := Subgroup.isClosed_of_discrete

scoped instance countable_Pr : Countable ↥(Pr F) := by
  haveI : Countable F := Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.symm.toEquiv
  haveI : Countable Fˣ := Units.val_injective.countable
  unfold Pr M4aHerbrand.principalIdeles
  exact (MonoidHom.rangeRestrict_surjective _).countable

@[reducible] def borelC : MeasurableSpace (C F) := borel _

attribute [local instance 2000] borelC

theorem borelSpace_C : @BorelSpace (C F) _ (borelC F) := @BorelSpace.mk _ _ (borelC F) rfl

attribute [local instance 2000] borelSpace_C

abbrev π : I F → C F := QuotientGroup.mk

theorem continuous_π : Continuous (π F) := QuotientGroup.continuous_mk

theorem measurable_π : Measurable (π F) := (continuous_π F).measurable

variable {F}

theorem ideleNorm_eq_one_of_mem {γ : I F} (hγ : γ ∈ Pr F) : ideleNorm F γ = 1 := by
  obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hγ
  have hpf : distribHaarChar (AdeleRing (𝓞 F) F)
      ((Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)) u) = 1 :=
    NumberField.AdeleRing.distribHaarChar_algebraMap F u
  show ((distribHaarChar (AdeleRing (𝓞 F) F) _ : ℝ≥0) : ℝ) = 1
  rw [hpf, NNReal.coe_one]

theorem ideleNorm_mul_of_mem {γ : I F} (hγ : γ ∈ Pr F) (t : I F) : ideleNorm F (γ * t) = ideleNorm F t := by
  rw [ideleNorm_mul, ideleNorm_eq_one_of_mem hγ, one_mul]

variable (F)

def normBar : C F → ℝ := fun c =>
  Quotient.liftOn' c (fun t : I F => ideleNorm F t) (fun a b hab => by
    have hab' : a⁻¹ * b ∈ Pr F := QuotientGroup.leftRel_apply.mp hab
    have : b = (a⁻¹ * b) * a := by rw [mul_comm, mul_inv_cancel_left]
    show ideleNorm F a = ideleNorm F b
    rw [this, ideleNorm_mul_of_mem hab'])

theorem normBar_mk (t : I F) : normBar F (π F t) = ideleNorm F t := rfl

theorem continuous_normBar : Continuous (normBar F) := by
  rw [← QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff]
  exact NumberField.TateGlobal.continuous_ideleNorm F

theorem normBar_pos (c : C F) : 0 < normBar F c := by
  obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective c
  exact ideleNorm_pos t

theorem exists_isHaarMeasure_map_restrict (D : Set (I F)) (hDm : MeasurableSet D)
    (hDF : IsFundamentalDomain (↥(Pr F)) D (NumberField.Idele.idelicHaar F)) :
    ∃ ν : Measure (C F), ν.IsHaarMeasure ∧ Measure.map (π F) ((NumberField.Idele.idelicHaar F).restrict D) = ν := by
  obtain ⟨-, -, -, ν, hν, hmap⟩ :=
    NumberField.Idele.t2Space_and_secondCountable_and_locallyCompact_and_exists_isHaarMeasure_map_mk_restrict_of_isFundamentalDomain
      F D hDm hDF
  exact ⟨ν, hν, hmap⟩

theorem mk_mul_of_mem_left {γ : I F} (hγ : γ ∈ Pr F) (t : I F) : π F (γ * t) = π F t := by
  rw [mul_comm]
  exact QuotientGroup.mk_mul_of_mem t hγ

abbrev wt : I F → ℝ≥0∞ := fun t => ENNReal.ofReal ((ideleNorm F t)⁻¹)

theorem measurable_wt : Measurable (wt F) :=
  ENNReal.measurable_ofReal.comp
    ((NumberField.TateGlobal.continuous_ideleNorm F).measurable.inv)

theorem isFiniteMeasureOnCompacts_map (D : Set (I F)) (hDm : MeasurableSet D)
    (hDF : IsFundamentalDomain (Pr F) D (NumberField.Idele.idelicHaar F)) :
    IsFiniteMeasureOnCompacts
      (Measure.map (π F) (((NumberField.Idele.idelicHaar F).restrict D).withDensity (wt F))) := by
  obtain ⟨ν, hν, hmap⟩ := exists_isHaarMeasure_map_restrict F D hDm hDF
  refine ⟨fun L hL => ?_⟩
  have hLm : MeasurableSet L := hL.isClosed.measurableSet
  rw [Measure.map_apply (measurable_π F) hLm, withDensity_apply _ (hLm.preimage (measurable_π F))]
  rcases L.eq_empty_or_nonempty with hLe | hLne
  · simp [hLe]
  obtain ⟨c₀, -, hc₀⟩ := hL.exists_isMinOn hLne (continuous_normBar F).continuousOn
  have hm0 : 0 < normBar F c₀ := normBar_pos F c₀
  have hbound : ∀ t ∈ (π F) ⁻¹' L, wt F t ≤ ENNReal.ofReal (normBar F c₀)⁻¹ := by
    intro t ht
    apply ENNReal.ofReal_le_ofReal
    have h1 : normBar F c₀ ≤ ideleNorm F t := by
      have := (isMinOn_iff.mp hc₀) (π F t) ht
      rwa [normBar_mk] at this
    exact inv_anti₀ hm0 h1
  have hfin : ν L < ∞ := hL.measure_lt_top
  calc ∫⁻ t in (π F) ⁻¹' L, wt F t ∂((NumberField.Idele.idelicHaar F).restrict D)
      ≤ ∫⁻ t in (π F) ⁻¹' L, ENNReal.ofReal (normBar F c₀)⁻¹ ∂((NumberField.Idele.idelicHaar F).restrict D) :=
        setLIntegral_mono measurable_const hbound
    _ = ENNReal.ofReal (normBar F c₀)⁻¹ * ((NumberField.Idele.idelicHaar F).restrict D) ((π F) ⁻¹' L) :=
        setLIntegral_const _ _
    _ = ENNReal.ofReal (normBar F c₀)⁻¹ * (Measure.map (π F) ((NumberField.Idele.idelicHaar F).restrict D)) L := by
        rw [Measure.map_apply (measurable_π F) hLm]
    _ = ENNReal.ofReal (normBar F c₀)⁻¹ * ν L := by rw [hmap]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

theorem exists_continuous_invariant_eLpNorm_sub_le (D : Set (I F)) (hDm : MeasurableSet D)
    (hDF : IsFundamentalDomain (Pr F) D (NumberField.Idele.idelicHaar F))
    (f : I F × KK F → ℂ)
    (hfinv : ∀ γ ∈ Pr F, ∀ p : I F × KK F, f (γ * p.1, p.2) = f p)
    (hf2 : MemLp f 2 ((((NumberField.Idele.idelicHaar F).restrict D).withDensity (wt F)).prod (maximalCompactHaar F)))
    (ε : ℝ≥0∞) (hε : ε ≠ 0) :
    ∃ G : I F × KK F → ℂ, Continuous G ∧ (∀ γ ∈ Pr F, ∀ p : I F × KK F, G (γ * p.1, p.2) = G p) ∧
      eLpNorm (f - G) 2 ((((NumberField.Idele.idelicHaar F).restrict D).withDensity (wt F)).prod (maximalCompactHaar F)) ≤ ε := by
  classical
  set μ := NumberField.Idele.idelicHaar F with hμ
  set μD := (μ.restrict D).withDensity (wt F) with hμD
  set ρ := μD.prod (maximalCompactHaar F) with hρ
  set ν₁ := Measure.map (π F) μD with hν₁
  set ν := ν₁.prod (maximalCompactHaar F) with hν
  haveI : BorelSpace (C F × KK F) := Prod.borelSpace
  haveI : BorelSpace (I F × KK F) := Prod.borelSpace
  haveI : SFinite μD := by rw [hμD]; infer_instance
  haveI : IsFiniteMeasureOnCompacts ν₁ := by rw [hν₁, hμD]; exact isFiniteMeasureOnCompacts_map F D hDm hDF
  haveI : IsLocallyFiniteMeasure ν₁ := inferInstance
  haveI : IsLocallyFiniteMeasure ν := by rw [hν]; infer_instance
  haveI : ν.Regular := inferInstance
  have hPim : Measurable (Prod.map (π F) (id : KK F → KK F)) := (measurable_π F).prodMap measurable_id
  have hρν : Measure.map (Prod.map (π F) (id : KK F → KK F)) ρ = ν := by
    rw [hν, hν₁, hρ, ← Measure.map_prod_map _ _ (measurable_π F) measurable_id, Measure.map_id]

  have hmapσ : MeasurableSpace.map (Prod.map (π F) (id : KK F → KK F)) (inferInstance : MeasurableSpace (I F × KK F))
      = borel (C F × KK F) :=
    ((continuous_π F).prodMap continuous_id).map_eq_borel
      (QuotientGroup.mk_surjective.prodMap Function.surjective_id)

  let P : (I F × KK F → ℂ) → Prop := fun g =>
    Continuous g ∧ ∀ γ ∈ Pr F, ∀ p : I F × KK F, g (γ * p.1, p.2) = g p
  have h1P : ∀ g g', P g → P g' → P (g + g') := by
    intro g g' hg hg'
    exact ⟨hg.1.add hg'.1, fun γ hγ p => by simp only [Pi.add_apply, hg.2 γ hγ p, hg'.2 γ hγ p]⟩
  have h2P : ∀ g, P g → AEStronglyMeasurable g ρ := fun g hg =>
    NumberField.Idele.aestronglyMeasurable_of_continuous_prod_maximalCompact F D hDm g hg.1
  have h0P : ∀ (c : ℂ) ⦃s : Set (I F × KK F)⦄, MeasurableSet s → ρ s < ∞ →
      ∀ {ε : ℝ≥0∞}, ε ≠ 0 → ∃ g : I F × KK F → ℂ, eLpNorm (g - s.indicator fun _ => c) 2 ρ ≤ ε ∧ P g := by
    intro c s hs hρs ε hε

    set S : Set (I F × KK F) :=
      ⋃ γ : ↥(Pr F), (fun p : I F × KK F => ((γ : I F) * p.1, p.2)) ⁻¹' (s ∩ (D ×ˢ Set.univ)) with hS
    have hmeasγ : ∀ γ : ↥(Pr F), Measurable (fun p : I F × KK F => ((γ : I F) * p.1, p.2)) := fun γ =>
      ((continuous_const.mul continuous_fst).prodMk continuous_snd).measurable
    have hSmeas : MeasurableSet S :=
      MeasurableSet.iUnion fun γ => (hs.inter (hDm.prod MeasurableSet.univ)).preimage (hmeasγ γ)
    have hmemS : ∀ p : I F × KK F, p ∈ S ↔ ∃ γ : ↥(Pr F), ((γ : I F) * p.1, p.2) ∈ s ∧ (γ : I F) * p.1 ∈ D := by
      intro p
      simp only [hS, Set.mem_iUnion, Set.mem_preimage, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, and_true]
    have hSinv : ∀ γ ∈ Pr F, ∀ p : I F × KK F, (γ * p.1, p.2) ∈ S ↔ p ∈ S := by
      intro γ hγ p
      rw [hmemS, hmemS]
      constructor
      · rintro ⟨γ', h1, h2⟩
        refine ⟨γ' * ⟨γ, hγ⟩, ?_, ?_⟩ <;> simpa [mul_assoc] using ‹_›
      · rintro ⟨γ', h1, h2⟩
        refine ⟨γ' * ⟨γ, hγ⟩⁻¹, ?_, ?_⟩ <;>
          simp only [Subgroup.coe_mul, InvMemClass.coe_inv, mul_assoc, inv_mul_cancel_left] <;> assumption

    have hae_set : ∀ᵐ p ∂ρ, p ∈ S ↔ p ∈ s := by

      set Bad : Set (I F) := Dᶜ ∪ ⋃ γ : ↥(Pr F), {t | γ ≠ 1 ∧ t ∈ D ∧ (γ : I F) * t ∈ D} with hBad
      have hBadm : MeasurableSet Bad := by
        refine hDm.compl.union (MeasurableSet.iUnion fun γ => ?_)
        by_cases hγ : γ = 1
        · have : {t : I F | γ ≠ 1 ∧ t ∈ D ∧ (γ : I F) * t ∈ D} = ∅ := by
            ext t; simp [hγ]
          rw [this]; exact MeasurableSet.empty
        · have : {t : I F | γ ≠ 1 ∧ t ∈ D ∧ (γ : I F) * t ∈ D} = D ∩ (fun t => (γ : I F) * t) ⁻¹' D := by
            ext t; simp [hγ]
          rw [this]
          exact hDm.inter (hDm.preimage (measurable_const_mul _))
      have hμBad : μ (Bad ∩ D) = 0 := by
        have hsub : Bad ∩ D ⊆ ⋃ γ : ↥(Pr F), {t | γ ≠ 1 ∧ t ∈ D ∧ (γ : I F) * t ∈ D} := by
          rintro t ⟨ht, htD⟩
          rcases ht with ht | ht
          · exact absurd htD ht
          · exact ht
        refine measure_mono_null hsub ?_
        rw [measure_iUnion_null_iff]
        intro γ
        by_cases hγ : γ = 1
        · have : {t : I F | γ ≠ 1 ∧ t ∈ D ∧ (γ : I F) * t ∈ D} = ∅ := by
            ext t; simp [hγ]
          rw [this, measure_empty]
        ·
          have hne : γ⁻¹ ≠ (1 : ↥(Pr F)) := by simpa using hγ
          have hdis := hDF.aedisjoint hne
          have hsub2 : {t : I F | γ ≠ 1 ∧ t ∈ D ∧ (γ : I F) * t ∈ D} ⊆ (γ⁻¹ • D) ∩ ((1 : ↥(Pr F)) • D) := by
            rintro t ⟨-, htD, hγt⟩
            refine ⟨?_, ?_⟩
            · rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv, Subgroup.smul_def, smul_eq_mul]
              exact hγt
            · rw [one_smul]; exact htD
          exact measure_mono_null hsub2 hdis
      have hρBad : ρ (Bad ×ˢ (Set.univ : Set (KK F))) = 0 := by
        rw [hρ, Measure.prod_prod, hμD]
        have : (μ.restrict D).withDensity (wt F) Bad = 0 := by
          apply withDensity_absolutelyContinuous
          rw [Measure.restrict_apply' hDm]
          exact hμBad
        rw [this, zero_mul]
      rw [ae_iff]
      refine measure_mono_null ?_ hρBad
      intro p hp
      simp only [Set.mem_setOf_eq, not_iff] at hp
      simp only [Set.mem_prod, Set.mem_univ, and_true]

      by_cases hpD : p.1 ∈ D
      · by_cases hps : p ∈ s
        ·
          exfalso
          have : p ∈ S := (hmemS p).mpr ⟨1, by simpa using hps, by simpa using hpD⟩
          exact (hp.mpr hps) this
        · have hpS : p ∈ S := by
            by_contra hcon
            exact hps (hp.mp hcon)
          obtain ⟨γ, h1, h2⟩ := (hmemS p).mp hpS
          have hγ : γ ≠ 1 := by
            rintro rfl
            exact hps (by simpa using h1)
          right
          exact Set.mem_iUnion.mpr ⟨γ, hγ, hpD, h2⟩
      · left; exact hpD
    have hae_set' : (S : Set (I F × KK F)) =ᵐ[ρ] s :=
      hae_set.mono fun p hp => by simp only [eq_iff_iff] at hp ⊢; exact hp

    set E : Set (C F × KK F) := {q | ∃ p ∈ S, (π F p.1, p.2) = q} with hE
    have hpre : (Prod.map (π F) (id : KK F → KK F)) ⁻¹' E = S := by
      ext p
      constructor
      · rintro ⟨p', hp'S, hpp'⟩
        have h1 : π F p'.1 = π F p.1 := by simpa using congrArg Prod.fst hpp'
        have h2 : p'.2 = p.2 := by simpa using congrArg Prod.snd hpp'

        have hrel : (p.1)⁻¹ * p'.1 ∈ Pr F := QuotientGroup.eq.mp h1.symm
        have hp' : p' = ((p.1)⁻¹ * p'.1 * p.1, p.2) :=
          Prod.ext (by rw [mul_comm ((p.1)⁻¹ * p'.1) p.1, mul_inv_cancel_left]) h2
        rw [hp'] at hp'S
        exact (hSinv _ hrel p).mp hp'S
      · intro hpS
        exact ⟨p, hpS, rfl⟩
    have hEmeas : MeasurableSet E := by
      have h1 : @MeasurableSet _ (MeasurableSpace.map (Prod.map (π F) (id : KK F → KK F))
          (inferInstance : MeasurableSpace (I F × KK F))) E := by
        show MeasurableSet ((Prod.map (π F) (id : KK F → KK F)) ⁻¹' E)
        rw [hpre]; exact hSmeas
      rw [hmapσ] at h1
      rwa [BorelSpace.measurable_eq (α := C F × KK F)]
    have hνE : ν E < ∞ := by
      rw [← hρν, Measure.map_apply hPim hEmeas, hpre, measure_congr hae_set']
      exact hρs

    have hmem : MemLp (E.indicator fun _ => c) 2 ν := memLp_indicator_const 2 hEmeas c (Or.inr hνE.ne)
    obtain ⟨h, -, hh, hhc, -⟩ := hmem.exists_hasCompactSupport_eLpNorm_sub_le ENNReal.ofNat_ne_top hε

    refine ⟨h ∘ Prod.map (π F) (id : KK F → KK F), ?_, hhc.comp ((continuous_π F).prodMap continuous_id), ?_⟩
    · have hind : (S.indicator fun _ => c) = (E.indicator fun _ => c) ∘ Prod.map (π F) (id : KK F → KK F) := by
        rw [← hpre]; rfl
      have haesm : AEStronglyMeasurable (h - E.indicator fun _ => c) (Measure.map (Prod.map (π F) (id : KK F → KK F)) ρ) := by
        rw [hρν]
        exact hhc.aestronglyMeasurable.sub ((aestronglyMeasurable_const).indicator hEmeas)
      calc eLpNorm (h ∘ Prod.map (π F) (id : KK F → KK F) - s.indicator fun _ => c) 2 ρ
          = eLpNorm (h ∘ Prod.map (π F) (id : KK F → KK F) - S.indicator fun _ => c) 2 ρ :=
            eLpNorm_congr_ae ((Filter.EventuallyEq.rfl).sub (indicator_ae_eq_of_ae_eq_set hae_set').symm)
        _ = eLpNorm ((h - E.indicator fun _ => c) ∘ Prod.map (π F) (id : KK F → KK F)) 2 ρ := by
            rw [hind]; rfl
        _ = eLpNorm (h - E.indicator fun _ => c) 2 (Measure.map (Prod.map (π F) (id : KK F → KK F)) ρ) :=
            (eLpNorm_map_measure haesm hPim.aemeasurable).symm
        _ = eLpNorm (h - E.indicator fun _ => c) 2 ν := by rw [hρν]
        _ = eLpNorm ((E.indicator fun _ => c) - h) 2 ν := eLpNorm_sub_comm _ _ _ _
        _ ≤ ε := hh
    · intro γ hγ p
      show h (π F (γ * p.1), id p.2) = h (π F p.1, id p.2)
      rw [mk_mul_of_mem_left F hγ]
  obtain ⟨G, hG, hPG⟩ := hf2.induction_dense ENNReal.ofNat_ne_top P h0P h1P h2P hε
  exact ⟨G, hPG.1, hPG.2, hG⟩

end Ws31.S1a
p2m_reactivate "P2MW.S_AutomorphicForm_exists_continuous_forall_principalIdeles_eLpNorm_sub_lt_of_memLp_withDensity_ideleNorm_inv_prod_maximalCompactHaar.Ws31 P2MW.S_AutomorphicForm_exists_continuous_forall_principalIdeles_eLpNorm_sub_lt_of_memLp_withDensity_ideleNorm_inv_prod_maximalCompactHaar.Ws31.S1a"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_continuous_forall_principalIdeles_eLpNorm_sub_lt_of_memLp_withDensity_ideleNorm_inv_prod_maximalCompactHaar.Ws31"

attribute [local instance 2000] Ws31.S1a.borelC Ws31.S1a.borelSpace_C

open Ws31.S1a in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdeleRing (𝓞 F) F)ˣ) (hDm : MeasurableSet D)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    (f : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) → ℂ)
    (hfinv : ∀ γ ∈ M4aHerbrand.principalIdeles (𝓞 F) F, ∀ p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F), f (γ * p.1, p.2) = f p)
    (hf2 : MemLp f 2
      ((((NumberField.Idele.idelicHaar F).restrict D).withDensity
          (fun t : (AdeleRing (𝓞 F) F)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹))).prod
        (maximalCompactHaar F)))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ G : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) → ℂ, Continuous G ∧
      (∀ γ ∈ M4aHerbrand.principalIdeles (𝓞 F) F, ∀ p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F), G (γ * p.1, p.2) = G p) ∧
      eLpNorm (fun p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) => f p - G p) 2
        ((((NumberField.Idele.idelicHaar F).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 F) F)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹))).prod
          (maximalCompactHaar F)) < ENNReal.ofReal δ := by
  have hδ2 : (ENNReal.ofReal (δ / 2)) ≠ 0 := by
    simpa [ENNReal.ofReal_eq_zero, not_le] using half_pos hδ
  obtain ⟨G, hGc, hGinv, hG⟩ :=
    Ws31.S1a.exists_continuous_invariant_eLpNorm_sub_le F D hDm hDF f hfinv hf2 (ENNReal.ofReal (δ / 2)) hδ2
  refine ⟨G, hGc, hGinv, lt_of_le_of_lt hG ?_⟩
  exact (ENNReal.ofReal_lt_ofReal_iff hδ).mpr (half_lt_self hδ)

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_continuous_forall_principalIdeles_eLpNorm_sub_lt_of_memLp_withDensity_ideleNorm_inv_prod_maximalCompactHaar.Ws31 P2MW.S_AutomorphicForm_exists_continuous_forall_principalIdeles_eLpNorm_sub_lt_of_memLp_withDensity_ideleNorm_inv_prod_maximalCompactHaar.Ws31.S1a"

end S_AutomorphicForm_exists_continuous_forall_principalIdeles_eLpNorm_sub_lt_of_memLp_withDensity_ideleNorm_inv_prod_maximalCompactHaar
end P2MW
export P2MW.S_AutomorphicForm_exists_continuous_forall_principalIdeles_eLpNorm_sub_lt_of_memLp_withDensity_ideleNorm_inv_prod_maximalCompactHaar (solution)
