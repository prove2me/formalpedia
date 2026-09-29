-- Prove2me | solution 1 for AutomorphicForm.TwistedBruhat.integral_transversal_tracePushforward_eq_tracePushforward_integral_of_bound
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/01e979e6-e28a-5fcf-b480-ee4d5251cd97

import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_AdelicTracePushforward
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_TwistedBruhat_integral_transversal_tracePushforward_eq_tracePushforward_integral_of_bound
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm AutomorphicForm.AdelicTracePushforward
open scoped TensorProduct Pointwise ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

namespace FubTrace

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

abbrev W : Type := Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K

abbrev μW : Measure (W K L) := Measure.pi fun _ => adelicAddHaar (𝓞 K) K

theorem secondCountableTopology_idele'' : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := by
  haveI := NumberField.AdeleRing.secondCountableTopology L
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := AdeleRing (𝓞 L) L)).symm.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

theorem sigmaCompactSpace_idele : SigmaCompactSpace (AdeleRing (𝓞 L) L)ˣ := by
  haveI := secondCountableTopology_idele'' L
  haveI : LocallyCompactSpace (AdeleRing (𝓞 L) L)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  exact sigmaCompactSpace_of_locallyCompact_secondCountable

theorem μW_lt_top_of_isCompact {C : Set (W K L)} (hC : IsCompact C) : μW K L C < ⊤ := by
  haveI : SigmaFinite (adelicAddHaar (𝓞 K) K) := by
    haveI := NumberField.AdeleRing.secondCountableTopology K
    unfold adelicAddHaar; infer_instance
  have hsub : C ⊆ Set.pi Set.univ fun i => (fun w : W K L => w i) '' C := by
    intro w hw i _; exact ⟨w, hw, rfl⟩
  refine lt_of_le_of_lt (measure_mono hsub) ?_
  rw [Measure.pi_pi]
  refine ENNReal.prod_lt_top fun i _ => ?_
  have hIFC : IsFiniteMeasureOnCompacts (adelicAddHaar (𝓞 K) K) := by unfold adelicAddHaar; infer_instance
  exact (hC.image (continuous_apply i)).measure_lt_top

theorem fubini_core (ν : Measure (AdeleRing (𝓞 L) L)ˣ) [IsFiniteMeasureOnCompacts ν] [SFinite ν]
    (τ : Measure (AdeleRing (𝓞 L) L)ˣ) (hτ : IsFiniteMeasureOnCompacts τ)
    (ξ : (AdeleRing (𝓞 L) L)ˣ → ℂ) (hξ : Continuous ξ)
    (g : (AdeleRing (𝓞 L) L)ˣ → ↥(adelicMaximalCompact L) → (AdeleRing (𝓞 L) L)ˣ → W K L → ℂ)
    (hgc : Continuous fun p : ((AdeleRing (𝓞 L) L)ˣ × ↥(adelicMaximalCompact L)) × ((AdeleRing (𝓞 L) L)ˣ × W K L) =>
      g p.1.1 p.1.2 p.2.1 p.2.2)
    (Ct Cz : Set (AdeleRing (𝓞 L) L)ˣ) (Cw : Set (W K L)) (hCt : IsCompact Ct) (hCz : IsCompact Cz)
    (hCw : IsCompact Cw) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ t k ζ w', ‖g t k ζ w'‖ ≤ M)
    (hz1 : ∀ t k ζ w', ζ ∉ Cz → g t k ζ w' = 0)
    (hz2 : ∀ᵐ t ∂τ, t ∉ Ct → ∀ k ζ w', g t k ζ w' = 0)
    (hz3 : ∀ t ∈ Ct, ∀ k ζ w', w' ∉ Cw → g t k ζ w' = 0) :
    (∫⁻ t, ∫⁻ k, ∫⁻ ζ, ‖ξ ζ * ∫ w', g t k ζ w' ∂(μW K L)‖ₑ ∂ν ∂(maximalCompactHaar L) ∂τ) ≠ ⊤ ∧
    (∫ t, ∫ k, (∫ ζ, ξ ζ * ∫ w', g t k ζ w' ∂(μW K L) ∂ν) ∂(maximalCompactHaar L) ∂τ) =
      ∫ w', ∫ t, ∫ k, (∫ ζ, ξ ζ * g t k ζ w' ∂ν) ∂(maximalCompactHaar L) ∂τ ∂(μW K L) := by

  haveI := secondCountableTopology_idele'' L
  haveI := sigmaCompactSpace_idele L
  haveI := NumberField.AdeleRing.secondCountableTopology K
  haveI := NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo L
  haveI : SigmaFinite τ := by haveI := hτ; infer_instance
  haveI : SigmaFinite (adelicAddHaar (𝓞 K) K) := by unfold adelicAddHaar; infer_instance
  set μk : Measure ↥(adelicMaximalCompact L) := maximalCompactHaar L with hμk

  set Ψ : ((AdeleRing (𝓞 L) L)ˣ × (↥(adelicMaximalCompact L) × (AdeleRing (𝓞 L) L)ˣ)) × W K L → ℂ :=
    fun p => ξ p.1.2.2 * g p.1.1 p.1.2.1 p.1.2.2 p.2 with hΨ
  have hΨc : Continuous Ψ := by
    refine Continuous.mul (hξ.comp (continuous_snd.comp (continuous_snd.comp continuous_fst))) ?_
    exact hgc.comp ((continuous_fst.fst.prodMk continuous_fst.snd.fst).prodMk
      (continuous_fst.snd.snd.prodMk continuous_snd))
  have hΨm : Measurable Ψ := hΨc.measurable

  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ ζ ∈ Cz, ‖ξ ζ‖ ≤ B := by
    obtain ⟨B, hB⟩ := (hCz.image hξ).isBounded.exists_norm_le
    exact ⟨B, fun ζ hζ => hB _ ⟨ζ, hζ, rfl⟩⟩
  have hB0 : 0 ≤ max B 0 := le_max_right _ _

  set μQ : Measure ((AdeleRing (𝓞 L) L)ˣ × (↥(adelicMaximalCompact L) × (AdeleRing (𝓞 L) L)ˣ)) :=
    τ.prod (μk.prod ν) with hμQ
  set μP : Measure (((AdeleRing (𝓞 L) L)ˣ × (↥(adelicMaximalCompact L) × (AdeleRing (𝓞 L) L)ˣ)) × W K L) :=
    μQ.prod (μW K L) with hμP
  set S : Set (((AdeleRing (𝓞 L) L)ˣ × (↥(adelicMaximalCompact L) × (AdeleRing (𝓞 L) L)ˣ)) × W K L) :=
    (Ct ×ˢ ((Set.univ : Set ↥(adelicMaximalCompact L)) ×ˢ Cz)) ×ˢ Cw with hS
  have hSm : MeasurableSet S :=
    ((hCt.isClosed.measurableSet.prod (MeasurableSet.univ.prod hCz.isClosed.measurableSet)).prod
      hCw.isClosed.measurableSet)
  have hμS : μP S < ⊤ := by
    simp only [hμP, hμQ, hS, Measure.prod_prod]
    have h1 : τ Ct < ⊤ := hτ.lt_top_of_isCompact hCt
    have h2 : μk Set.univ < ⊤ := measure_lt_top _ _
    have h3 : ν Cz < ⊤ := hCz.measure_lt_top
    have h4 : μW K L Cw < ⊤ := μW_lt_top_of_isCompact K L hCw
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top h1 (ENNReal.mul_lt_top h2 h3)) h4

  have hz2' : ∀ᵐ p ∂μP, p.1.1 ∉ Ct → ∀ k ζ w', g p.1.1 k ζ w' = 0 := by
    have hq : Measure.QuasiMeasurePreserving
        (fun p : ((AdeleRing (𝓞 L) L)ˣ × (↥(adelicMaximalCompact L) × (AdeleRing (𝓞 L) L)ˣ)) × W K L => p.1.1) μP τ :=
      (Measure.quasiMeasurePreserving_fst (μ := τ) (ν := μk.prod ν)).comp
        (Measure.quasiMeasurePreserving_fst (μ := μQ) (ν := μW K L))
    exact hq.ae hz2
  have hdom : ∀ᵐ p ∂μP, ‖Ψ p‖ ≤ S.indicator (fun _ => max B 0 * M) p := by
    filter_upwards [hz2'] with p hp
    have hnn : 0 ≤ S.indicator (fun _ => max B 0 * M) p :=
      Set.indicator_nonneg (fun _ _ => mul_nonneg hB0 hM) _
    by_cases ht : p.1.1 ∈ Ct
    · by_cases hζ : p.1.2.2 ∈ Cz
      · by_cases hw : p.2 ∈ Cw
        · have hmem : p ∈ S := by
            simp only [hS, Set.mem_prod, Set.mem_univ, true_and]
            exact ⟨⟨ht, hζ⟩, hw⟩
          rw [Set.indicator_of_mem hmem]
          simp only [hΨ, norm_mul]
          exact mul_le_mul ((hB _ hζ).trans (le_max_left _ _)) (hb _ _ _ _) (norm_nonneg _) hB0
        · have : Ψ p = 0 := by simp only [hΨ, hz3 _ ht _ _ _ hw, mul_zero]
          rw [this, norm_zero]; exact hnn
      · have : Ψ p = 0 := by simp only [hΨ, hz1 _ _ _ _ hζ, mul_zero]
        rw [this, norm_zero]; exact hnn
    · have : Ψ p = 0 := by simp only [hΨ, hp ht, mul_zero]
      rw [this, norm_zero]; exact hnn
  have hgI : Integrable (S.indicator fun _ => max B 0 * M) μP := by
    refine IntegrableOn.integrable_indicator ?_ hSm
    exact integrableOn_const hμS.ne
  have hΨi : Integrable Ψ μP := hgI.mono' hΨm.aestronglyMeasurable hdom

  have hI : Integrable (fun q => ∫ w', Ψ (q, w') ∂(μW K L)) μQ := hΨi.integral_prod_left
  have lhs : (∫ t, ∫ k, (∫ ζ, ξ ζ * ∫ w', g t k ζ w' ∂(μW K L) ∂ν) ∂μk ∂τ) = ∫ q, (∫ w', Ψ (q, w') ∂(μW K L)) ∂μQ := by
    rw [hμQ, integral_prod _ hI]
    refine integral_congr_ae ?_
    filter_upwards [hI.prod_right_ae] with t ht
    rw [integral_prod _ ht]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
    show ξ ζ * ∫ w', g t k ζ w' ∂(μW K L) = ∫ w', ξ ζ * g t k ζ w' ∂(μW K L)
    exact (integral_const_mul _ _).symm
  have rhs : (∫ w', ∫ t, ∫ k, (∫ ζ, ξ ζ * g t k ζ w' ∂ν) ∂μk ∂τ ∂(μW K L)) = ∫ w', (∫ q, Ψ (q, w') ∂μQ) ∂(μW K L) := by
    refine integral_congr_ae ?_
    filter_upwards [hΨi.prod_left_ae] with w' hw'
    rw [hμQ, integral_prod _ hw']
    refine integral_congr_ae ?_
    filter_upwards [hw'.prod_right_ae] with t ht
    rw [integral_prod _ ht]
  refine ⟨?_, ?_⟩
  ·
    have hfinP : ∫⁻ p, ‖Ψ p‖ₑ ∂μP < ⊤ := hΨi.2
    refine ne_top_of_le_ne_top hfinP.ne ?_
    rw [hμP, lintegral_prod _ hΨm.enorm.aemeasurable, hμQ,
      lintegral_prod _ (hΨm.enorm.lintegral_prod_right').aemeasurable]
    refine lintegral_mono fun t => ?_
    have hmt : Measurable fun q : ↥(adelicMaximalCompact L) × (AdeleRing (𝓞 L) L)ˣ =>
        ∫⁻ w', ‖Ψ ((t, q), w')‖ₑ ∂(μW K L) :=
      (hΨm.enorm.lintegral_prod_right').comp (measurable_const.prodMk measurable_id)
    rw [lintegral_prod _ hmt.aemeasurable]
    refine lintegral_mono fun k => lintegral_mono fun ζ => ?_
    show ‖ξ ζ * ∫ w', g t k ζ w' ∂(μW K L)‖ₑ ≤ ∫⁻ w', ‖ξ ζ * g t k ζ w'‖ₑ ∂(μW K L)
    rw [enorm_mul]
    simp_rw [enorm_mul]
    rw [lintegral_const_mul' _ _ enorm_ne_top]
    exact mul_le_mul' le_rfl (enorm_integral_le_lintegral_enorm _)
  ·
    rw [lhs, rhs, ← integral_prod _ hΨi, integral_prod_symm _ hΨi]

end FubTrace

namespace FubTrace

theorem fub_main
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (φ : AdelicGL2 (𝓞 L) L → ℂ)
    (τj : @Measure (AdeleRing (𝓞 L) L)ˣ (NumberField.Idele.ideleBorel L)) (hτfin : IsFiniteMeasureOnCompacts τj)
    (Ct : Set (AdeleRing (𝓞 L) L)ˣ) (Cz : Set (AdeleRing (𝓞 L) L)ˣ) (Cr : Set (AdeleRing (𝓞 K) K))
    (Cw : Set (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K)) (M : ℝ)
    (hsupp : IsCompact Ct ∧ IsCompact Cz ∧ IsCompact Cr ∧ IsCompact Cw ∧ 0 ≤ M ∧
      (∀ (t : (AdeleRing (𝓞 L) L)ˣ) (k : adelicMaximalCompact L) (ζ : (AdeleRing (𝓞 L) L)ˣ)
          (r : AdeleRing (𝓞 K) K) (w' : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K),
        ‖φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
              unipotentGL2 ((traceFibre K L r w') * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
              diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
              centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
              AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))‖ ≤ M) ∧
      (∀ (t : (AdeleRing (𝓞 L) L)ˣ) (k : adelicMaximalCompact L) (ζ : (AdeleRing (𝓞 L) L)ˣ)
          (r : AdeleRing (𝓞 K) K) (w' : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K),
        ζ ∉ Cz → φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
              unipotentGL2 ((traceFibre K L r w') * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
              diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
              centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
              AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)) = 0) ∧
      (∀ᵐ t ∂τj, t ∉ Ct → ∀ (k : adelicMaximalCompact L) (ζ : (AdeleRing (𝓞 L) L)ˣ)
          (r : AdeleRing (𝓞 K) K) (w' : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K),
        φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
              unipotentGL2 ((traceFibre K L r w') * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
              diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
              centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
              AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)) = 0) ∧
      (∀ t ∈ Ct, ∀ (k : adelicMaximalCompact L) (ζ : (AdeleRing (𝓞 L) L)ˣ)
          (r : AdeleRing (𝓞 K) K) (w' : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K),
        (r ∉ Cr ∨ w' ∉ Cw) → φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
              unipotentGL2 ((traceFibre K L r w') * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
              diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
              centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
              AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)) = 0) ∧
      Continuous (fun p : ((AdeleRing (𝓞 L) L)ˣ × ↥(adelicMaximalCompact L)) ×
          ((AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K ×
            (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K))) =>
        (fun (t : (AdeleRing (𝓞 L) L)ˣ) (k : adelicMaximalCompact L) (ζ : (AdeleRing (𝓞 L) L)ˣ)
            (r : AdeleRing (𝓞 K) K) (w' : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K) =>
          φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
              unipotentGL2 ((traceFibre K L r w') * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
              diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
              centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
              AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2))
    (r : AdeleRing (𝓞 K) K) :

    (∫⁻ t, ∫⁻ k, ∫⁻ ζ, ‖((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) *
          tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r‖ₑ ∂νZL ∂(maximalCompactHaar L) ∂τj) ≠ ⊤ ∧
    (∫ t, ∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) *
          tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r ∂νZL) ∂(maximalCompactHaar L) ∂τj) =
      tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
        ∫ t, ∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) *
          (φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) ∂νZL) ∂(maximalCompactHaar L) ∂τj) r := by
  have hm : ‹MeasurableSpace (AdeleRing (𝓞 L) L)ˣ› = NumberField.Idele.ideleBorel L := BorelSpace.measurable_eq
  subst hm
  haveI := secondCountableTopology_idele'' L
  haveI := sigmaCompactSpace_idele L
  haveI : LocallyCompactSpace (AdeleRing (𝓞 L) L)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI := NumberField.AdeleRing.secondCountableTopology K
  obtain ⟨hCt, hCz, hCr, hCw, hM, hb, hz1, hz2, hz3, hcont⟩ := hsupp
  have hmap : Continuous fun p : ((AdeleRing (𝓞 L) L)ˣ × ↥(adelicMaximalCompact L)) × ((AdeleRing (𝓞 L) L)ˣ × W K L) =>
      ((p.1.1, p.1.2), (p.2.1, (r, p.2.2))) :=
    (continuous_fst.fst.prodMk continuous_fst.snd).prodMk
      (continuous_snd.fst.prodMk (continuous_const.prodMk continuous_snd.snd))
  have hgc0 := hcont.comp hmap
  simp only [Function.comp_def] at hgc0
  have hgc : Continuous fun p : ((AdeleRing (𝓞 L) L)ˣ × ↥(adelicMaximalCompact L)) × ((AdeleRing (𝓞 L) L)ˣ × W K L) =>
      (fun (t : (AdeleRing (𝓞 L) L)ˣ) (k : ↥(adelicMaximalCompact L)) (ζ : (AdeleRing (𝓞 L) L)ˣ) (w' : W K L) =>
        φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 ((traceFibre K L r w') * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) p.1.1 p.1.2 p.2.1 p.2.2 := hgc0
  have key := fubini_core K L νZL τj hτfin (fun ζ => ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ)) hξc
    (fun (t : (AdeleRing (𝓞 L) L)ˣ) (k : ↥(adelicMaximalCompact L)) (ζ : (AdeleRing (𝓞 L) L)ˣ) (w' : W K L) =>
      φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 ((traceFibre K L r w') * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)))
    hgc Ct Cz Cw hCt hCz hCw M hM
    (fun t k ζ w' => hb t k ζ r w') (fun t k ζ w' h => hz1 t k ζ r w' h)
    (hz2.mono fun t ht => fun h k ζ w' => ht h k ζ r w')
    (fun t ht k ζ w' hw => hz3 t ht k ζ r w' (Or.inr hw))
  beta_reduce at key
  unfold tracePushforward
  exact key

end FubTrace

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (φ : AdelicGL2 (𝓞 L) L → ℂ)
    (τj : @Measure (AdeleRing (𝓞 L) L)ˣ (NumberField.Idele.ideleBorel L)) (hτfin : IsFiniteMeasureOnCompacts τj)
    (Ct : Set (AdeleRing (𝓞 L) L)ˣ) (Cz : Set (AdeleRing (𝓞 L) L)ˣ) (Cr : Set (AdeleRing (𝓞 K) K))
    (Cw : Set (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K)) (M : ℝ)
    (hsupp : IsCompact Ct ∧ IsCompact Cz ∧ IsCompact Cr ∧ IsCompact Cw ∧ 0 ≤ M ∧
      (∀ (t : (AdeleRing (𝓞 L) L)ˣ) (k : adelicMaximalCompact L) (ζ : (AdeleRing (𝓞 L) L)ˣ)
          (r : AdeleRing (𝓞 K) K) (w' : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K),
        ‖φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
              unipotentGL2 ((traceFibre K L r w') * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
              diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
              centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
              AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))‖ ≤ M) ∧
      (∀ (t : (AdeleRing (𝓞 L) L)ˣ) (k : adelicMaximalCompact L) (ζ : (AdeleRing (𝓞 L) L)ˣ)
          (r : AdeleRing (𝓞 K) K) (w' : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K),
        ζ ∉ Cz → φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
              unipotentGL2 ((traceFibre K L r w') * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
              diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
              centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
              AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)) = 0) ∧
      (∀ᵐ t ∂τj, t ∉ Ct → ∀ (k : adelicMaximalCompact L) (ζ : (AdeleRing (𝓞 L) L)ˣ)
          (r : AdeleRing (𝓞 K) K) (w' : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K),
        φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
              unipotentGL2 ((traceFibre K L r w') * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
              diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
              centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
              AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)) = 0) ∧
      (∀ t ∈ Ct, ∀ (k : adelicMaximalCompact L) (ζ : (AdeleRing (𝓞 L) L)ˣ)
          (r : AdeleRing (𝓞 K) K) (w' : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K),
        (r ∉ Cr ∨ w' ∉ Cw) → φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
              unipotentGL2 ((traceFibre K L r w') * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
              diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
              centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
              AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)) = 0) ∧
      Continuous (fun p : ((AdeleRing (𝓞 L) L)ˣ × ↥(adelicMaximalCompact L)) ×
          ((AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K ×
            (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K))) =>
        (fun (t : (AdeleRing (𝓞 L) L)ˣ) (k : adelicMaximalCompact L) (ζ : (AdeleRing (𝓞 L) L)ˣ)
            (r : AdeleRing (𝓞 K) K) (w' : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K) =>
          φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
              unipotentGL2 ((traceFibre K L r w') * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
              diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
              centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
              AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2))
    (r : AdeleRing (𝓞 K) K) :

    (∫⁻ t, ∫⁻ k, ∫⁻ ζ, ‖((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) *
          tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r‖ₑ ∂νZL ∂(maximalCompactHaar L) ∂τj) ≠ ⊤ ∧
    (∫ t, ∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) *
          tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r ∂νZL) ∂(maximalCompactHaar L) ∂τj) =
      tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
        ∫ t, ∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) *
          (φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) ∂νZL) ∂(maximalCompactHaar L) ∂τj) r :=
  FubTrace.fub_main K L νZL D σ ξL hξc φ τj hτfin Ct Cz Cr Cw M hsupp r

end
end S_AutomorphicForm_TwistedBruhat_integral_transversal_tracePushforward_eq_tracePushforward_integral_of_bound
end P2MW
export P2MW.S_AutomorphicForm_TwistedBruhat_integral_transversal_tracePushforward_eq_tracePushforward_integral_of_bound (solution)
