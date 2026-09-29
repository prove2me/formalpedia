-- Prove2me | solution 1 for AutomorphicForm.TwistedBruhat.integrableOn_and_integral_unipotentFold_eq_sum_mul_setIntegral_rankOne_of_invariance_of_dilation_of_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/9e7e917e-e8b7-57dd-9751-3e4bd2d8c401

import Mathlib
import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_AdelicTracePushforward
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_M4aHerbrand_GenuineBeta
import Theorems.Thm_AutomorphicForm_TransversalMeasure_setLIntegral_fundamentalDomain_inter_saturated_eq_mul_setLIntegral_lintegral_sum_of_transversal
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_TwistedBruhat_integrableOn_and_integral_unipotentFold_eq_sum_mul_setIntegral_rankOne_of_invariance_of_dilation_of_ne_top
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open AutomorphicForm.TransversalMeasure
open scoped ENNReal NNReal Topology

namespace G4CGlue

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

section Topology

variable (F : Type) [Field F] [NumberField F]

theorem secondCountableTopology_idele : SecondCountableTopology (AdeleRing (𝓞 F) F)ˣ := by
  haveI := NumberField.AdeleRing.secondCountableTopology F
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := AdeleRing (𝓞 F) F)).symm.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

theorem locallyCompactSpace_idele : LocallyCompactSpace (AdeleRing (𝓞 F) F)ˣ :=
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem sigmaCompactSpace_idele : SigmaCompactSpace (AdeleRing (𝓞 F) F)ˣ := by
  haveI := secondCountableTopology_idele F
  haveI := locallyCompactSpace_idele F
  exact sigmaCompactSpace_of_locallyCompact_secondCountable

end Topology

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem continuous_idelesBaseChange : Continuous (idelesBaseChange K L) :=
  Continuous.units_map _ (M4aHerbrand.Bridge.continuous_genuineβ K L)

theorem core
    (Sτ : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) (c : Fin n → ℝ)
    (τ : Fin n → Measure (AdeleRing (𝓞 L) L)ˣ) (cτ : ℝ≥0∞) (hcτ0 : cτ ≠ 0) (hcτT : cτ ≠ ⊤)
    (hcpos : ∀ j, 0 < c j)
    (hlev : ∀ j, τ j {t | NumberField.TateGlobal.ideleNorm L t ≠ c j} = 0)
    (hτfin : ∀ j, IsFiniteMeasureOnCompacts (τ j))
    (hmeas : MeasurableSet (saturated K L Sτ))
    (hmul : ∀ t ∈ saturated K L Sτ, ∀ s : (AdeleRing (𝓞 K) K)ˣ, t * idelesBaseChange K L s ∈ saturated K L Sτ)
    (hτ0 : ∀ j, τ j (saturated K L Sτ)ᶜ = 0)
    (hτ2 : ∀ E : Set (AdeleRing (𝓞 L) L)ˣ, MeasurableSet E → E ⊆ saturated K L Sτ →
      Measurable (fun s : (AdeleRing (𝓞 K) K)ˣ =>
        (∑ j, τ j) ((fun t => t * idelesBaseChange K L s) ⁻¹' E)) ∧
      NumberField.Idele.idelicHaar L E = cτ *
        ∫⁻ s : (AdeleRing (𝓞 K) K)ˣ, (∑ j, τ j) ((fun t => t * idelesBaseChange K L s) ⁻¹' E)
          ∂(NumberField.Idele.idelicHaar K))
    (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK
      (NumberField.Idele.idelicHaar K))
    (Ω : Set (AdeleRing (𝓞 L) L)ˣ) (hΩm : MeasurableSet Ω)
    (hΩ : IsFundamentalDomain
      ((idelesBaseChange K L).comp (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K))).range Ω
      (NumberField.Idele.idelicHaar L))
    (Fold : (AdeleRing (𝓞 L) L)ˣ → ℂ) (INNER' : (AdeleRing (𝓞 L) L)ˣ → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (INNER : Fin n → (AdeleRing (𝓞 L) L)ˣ → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hMEAS : Measurable Fold)
    (hINV : ∀ (q : Kˣ) (t : (AdeleRing (𝓞 L) L)ˣ),
      Fold (t * idelesBaseChange K L (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) q)) =
        Fold t)
    (hDIL : ∀ (t : (AdeleRing (𝓞 L) L)ˣ) (y : (AdeleRing (𝓞 K) K)ˣ),
      Fold (t * idelesBaseChange K L y) =
        (((NumberField.TateGlobal.ideleNorm L t)⁻¹ * (NumberField.TateGlobal.ideleNorm K y)⁻¹ : ℝ) : ℂ) * INNER' t y)
    (hthr : ∀ (j : Fin n) (t : (AdeleRing (𝓞 L) L)ˣ), NumberField.TateGlobal.ideleNorm L t = c j →
      ∀ y, INNER' t y = INNER j t y)
    (hsupp : ∀ t, t ∉ saturated K L Sτ → Fold t = 0)
    (hfin : ∫⁻ t in Ω, ‖Fold t‖ₑ ∂(NumberField.Idele.idelicHaar L) ≠ ⊤) :
    (∀ j : Fin n, IntegrableOn (fun y : (AdeleRing (𝓞 K) K)ˣ =>
        ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ)⁻¹ * ∫ t, INNER j t y ∂(τ j))
        ΩK (NumberField.Idele.idelicHaar K)) ∧
    ∫ t in Ω, Fold t ∂(NumberField.Idele.idelicHaar L) =
      ∑ j : Fin n, ((cτ.toReal * (c j)⁻¹ : ℝ) : ℂ) * ∫ y in ΩK,
        ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ)⁻¹ * ∫ t, INNER j t y ∂(τ j)
        ∂(NumberField.Idele.idelicHaar K) := by
  classical

  have hNpos : ∀ y : (AdeleRing (𝓞 K) K)ˣ, 0 < NumberField.TateGlobal.ideleNorm K y := fun y =>
    NumberField.TateGlobal.ideleNorm_pos y

  haveI := sigmaCompactSpace_idele L
  haveI := secondCountableTopology_idele L
  haveI := secondCountableTopology_idele K
  haveI : ∀ j, SigmaFinite (τ j) := fun j => by haveI := hτfin j; infer_instance

  have hbcm : Measurable (idelesBaseChange K L) := (continuous_idelesBaseChange K L).measurable
  have hjoint : Measurable fun p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 L) L)ˣ => Fold (p.2 * idelesBaseChange K L p.1) :=
    hMEAS.comp (measurable_snd.mul (hbcm.comp measurable_fst))
  have hslice : ∀ s : (AdeleRing (𝓞 K) K)ˣ, Measurable fun t : (AdeleRing (𝓞 L) L)ˣ => Fold (t * idelesBaseChange K L s) :=
    fun s => hMEAS.comp (measurable_mul_const _)
  have hsm : ∀ j, AEStronglyMeasurable (fun s : (AdeleRing (𝓞 K) K)ˣ => ∫ t, Fold (t * idelesBaseChange K L s) ∂(τ j))
      ((NumberField.Idele.idelicHaar K).restrict ΩK) := fun j =>
    (MeasureTheory.StronglyMeasurable.integral_prod_right' (ν := τ j)
      hjoint.stronglyMeasurable).aestronglyMeasurable

  obtain ⟨hQ1, hQ2⟩ :=
    AutomorphicForm.TransversalMeasure.setLIntegral_fundamentalDomain_inter_saturated_eq_mul_setLIntegral_lintegral_sum_of_transversal
      K L Sτ n τ cτ hmeas hmul hτfin hτ0 hτ2 ΩK hΩK Ω hΩm hΩ

  have hΩsat : ∫ t in Ω, Fold t ∂(NumberField.Idele.idelicHaar L) = ∫ t in Ω ∩ saturated K L Sτ, Fold t ∂(NumberField.Idele.idelicHaar L) :=
    setIntegral_eq_of_subset_of_forall_diff_eq_zero hΩm Set.inter_subset_left
      (fun t ht => hsupp t fun h => ht.2 ⟨ht.1, h⟩)
  have hfin' : ∫⁻ t in Ω ∩ saturated K L Sτ, ‖Fold t‖ₑ ∂(NumberField.Idele.idelicHaar L) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (lintegral_mono_set Set.inter_subset_left)
  have hId := hQ2 Fold hMEAS hINV hfin'
  have hAbs := hQ1 (fun t => ‖Fold t‖ₑ) hMEAS.enorm (fun k t => by simp only [hINV])

  have hfinK : ∫⁻ s in ΩK, ∫⁻ t, ‖Fold (t * idelesBaseChange K L s)‖ₑ ∂(∑ j, τ j) ∂(NumberField.Idele.idelicHaar K) ≠ ⊤ := by
    intro h
    apply hfin'
    rw [hAbs, h, ENNReal.mul_top hcτ0]
  have hfinj : ∀ j, ∫⁻ s in ΩK, ∫⁻ t, ‖Fold (t * idelesBaseChange K L s)‖ₑ ∂(τ j) ∂(NumberField.Idele.idelicHaar K) < ⊤ := by
    intro j
    refine lt_of_le_of_lt (lintegral_mono fun s => ?_) hfinK.lt_top
    rw [lintegral_finset_sum_measure]
    exact Finset.single_le_sum (f := fun i => ∫⁻ t, ‖Fold (t * idelesBaseChange K L s)‖ₑ ∂(τ i))
      (fun _ _ => bot_le) (Finset.mem_univ j)

  have hIntj : ∀ j, IntegrableOn (fun s => ∫ t, Fold (t * idelesBaseChange K L s) ∂(τ j)) ΩK (NumberField.Idele.idelicHaar K) := by
    intro j
    refine ⟨hsm j, ?_⟩
    refine lt_of_le_of_lt (lintegral_mono fun s => enorm_integral_le_lintegral_enorm _) (hfinj j)
  have hae_int : ∀ j, ∀ᵐ s ∂((NumberField.Idele.idelicHaar K).restrict ΩK), Integrable (fun t => Fold (t * idelesBaseChange K L s)) (τ j) := by
    intro j
    have hm : Measurable fun s : (AdeleRing (𝓞 K) K)ˣ => ∫⁻ t, ‖Fold (t * idelesBaseChange K L s)‖ₑ ∂(τ j) :=
      (hjoint.enorm).lintegral_prod_right'
    filter_upwards [ae_lt_top hm (hfinj j).ne] with s hs
    exact ⟨(hslice s).aestronglyMeasurable, hs⟩

  have hpiece : ∀ (j : Fin n) (s : (AdeleRing (𝓞 K) K)ˣ),
      ∫ t, Fold (t * idelesBaseChange K L s) ∂(τ j) =
        (((c j)⁻¹ * (NumberField.TateGlobal.ideleNorm K s)⁻¹ : ℝ) : ℂ) * ∫ t, INNER j t s ∂(τ j) := by
    intro j s
    have hae : ∀ᵐ t ∂(τ j), Fold (t * idelesBaseChange K L s) =
        (((c j)⁻¹ * (NumberField.TateGlobal.ideleNorm K s)⁻¹ : ℝ) : ℂ) * INNER j t s := by
      have hl : ∀ᵐ t ∂(τ j), t ∉ {t | NumberField.TateGlobal.ideleNorm L t ≠ c j} :=
        measure_eq_zero_iff_ae_notMem.1 (hlev j)
      filter_upwards [hl] with t ht
      have ht' : NumberField.TateGlobal.ideleNorm L t = c j := by
        simpa [Set.mem_setOf_eq] using ht
      rw [hDIL, ht', hthr j t ht' s]
    rw [integral_congr_ae hae, integral_const_mul]
  refine ⟨fun j => ?_, ?_⟩
  ·
    have heq : (fun y : (AdeleRing (𝓞 K) K)ˣ =>
        ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ)⁻¹ * ∫ t, INNER j t y ∂(τ j)) =
        fun y => ((c j : ℝ) : ℂ) * ∫ t, Fold (t * idelesBaseChange K L y) ∂(τ j) := by
      funext y
      rw [hpiece j y]
      have hy : ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hNpos y).ne'
      have hc : ((c j : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hcpos j).ne'
      push_cast
      field_simp
    rw [heq]
    exact (hIntj j).const_mul _
  ·
    rw [hΩsat, hId]
    have hsplit : ∫ s in ΩK, ∫ t, Fold (t * idelesBaseChange K L s) ∂(∑ j, τ j) ∂(NumberField.Idele.idelicHaar K) =
        ∑ j, ∫ s in ΩK, ∫ t, Fold (t * idelesBaseChange K L s) ∂(τ j) ∂(NumberField.Idele.idelicHaar K) := by
      rw [← integral_finset_sum _ (fun j _ => hIntj j)]
      refine integral_congr_ae ?_
      have hall : ∀ᵐ s ∂((NumberField.Idele.idelicHaar K).restrict ΩK), ∀ j, Integrable (fun t => Fold (t * idelesBaseChange K L s)) (τ j) :=
        ae_all_iff.2 fun j => hae_int j
      filter_upwards [hall] with s hs
      exact integral_finset_sum_measure fun j _ => hs j
    rw [hsplit, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hpt : (fun s : (AdeleRing (𝓞 K) K)ˣ => ∫ t, Fold (t * idelesBaseChange K L s) ∂(τ j)) =
        fun s => (((c j)⁻¹ : ℝ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K s : ℝ) : ℂ)⁻¹ * ∫ t, INNER j t s ∂(τ j)) := by
      funext s; rw [hpiece j s]; push_cast; ring
    rw [hpt, integral_const_mul]
    push_cast
    ring

end G4CGlue

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm AutomorphicForm.AdelicTracePushforward
open scoped TensorProduct Pointwise ENNReal

section Concrete

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem tracePushforward_zero_fun (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (r : AdeleRing (𝓞 K) K) : tracePushforward K L (fun _ : AdeleRing (𝓞 L) L => (0 : ℂ)) r = 0 := by
  simp [tracePushforward]

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) (R : ℝ)
    (Ω₂K : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩ₂Km : @MeasurableSet _ (NumberField.Idele.ideleBorel L) Ω₂K)
    (hΩ₂K : @IsFundamentalDomain
      ((AutomorphicForm.TransversalMeasure.idelesBaseChange K L).comp
        (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K))).range _ _ _
      (NumberField.Idele.ideleBorel L) Ω₂K (NumberField.Idele.idelicHaar L))
    [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
    (μK : Measure (AdeleRing (𝓞 K) K)) [μK.IsAddHaarMeasure]

    (Sτ : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) (c : Fin n → ℝ)
    (τ : Fin n → @Measure (AdeleRing (𝓞 L) L)ˣ (NumberField.Idele.ideleBorel L)) (cτ : ℝ≥0∞)
    (hcτ0 : cτ ≠ 0) (hcτT : cτ ≠ ⊤) (hcpos : ∀ j, 0 < c j)
    (hlev : ∀ j, τ j {t | NumberField.TateGlobal.ideleNorm L t ≠ c j} = 0)
    (hτfin : ∀ j, IsFiniteMeasureOnCompacts (τ j))
    (hmeas : @MeasurableSet (AdeleRing (𝓞 L) L)ˣ (NumberField.Idele.ideleBorel L)
      (AutomorphicForm.TransversalMeasure.saturated K L Sτ))
    (hmul : ∀ t ∈ AutomorphicForm.TransversalMeasure.saturated K L Sτ, ∀ s : (AdeleRing (𝓞 K) K)ˣ,
      t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L s ∈ AutomorphicForm.TransversalMeasure.saturated K L Sτ)
    (hτ0 : ∀ j, τ j (AutomorphicForm.TransversalMeasure.saturated K L Sτ)ᶜ = 0)
    (hτ2 : ∀ E : Set (AdeleRing (𝓞 L) L)ˣ, @MeasurableSet _ (NumberField.Idele.ideleBorel L) E →
      E ⊆ AutomorphicForm.TransversalMeasure.saturated K L Sτ →
      @Measurable _ _ (NumberField.Idele.ideleBorel K) _ (fun s : (AdeleRing (𝓞 K) K)ˣ =>
        (∑ j, τ j) ((fun t => t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L s) ⁻¹' E)) ∧
      NumberField.Idele.idelicHaar L E = cτ *
        ∫⁻ s : (AdeleRing (𝓞 K) K)ˣ,
          (∑ j, τ j) ((fun t => t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L s) ⁻¹' E)
          ∂(NumberField.Idele.idelicHaar K))

    (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : @IsFundamentalDomain (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range _ _ _
      (NumberField.Idele.ideleBorel K) ΩK (NumberField.Idele.idelicHaar K))

    (a : Fin n → ℝ) (b : ℝ)
    (hthr : ∀ (j : Fin n) (t : (AdeleRing (𝓞 L) L)ˣ), NumberField.TateGlobal.ideleNorm L t = c j →
      ∀ y : (AdeleRing (𝓞 K) K)ˣ,
        (Real.exp R < NumberField.AdelicHeight.adelicHeight L
            (diagOne (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) : AdelicGL2 (𝓞 L) L) ↔
          a j * Real.exp (b * R) < NumberField.TateGlobal.ideleNorm K y))

    (hDbc : ∀ y : (AdeleRing (𝓞 K) K)ˣ,
      M4aHerbrand.IdeleGaloisDescent.unitsAct D σ (AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) =
        AutomorphicForm.TransversalMeasure.idelesBaseChange K L y)

    (hsupp : ∀ t : (AdeleRing (𝓞 L) L)ˣ, t ∉ AutomorphicForm.TransversalMeasure.saturated K L Sτ →
      ∀ (k : adelicMaximalCompact L) (ζ : (AdeleRing (𝓞 L) L)ˣ) (w : AdeleRing (𝓞 L) L),
        φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)) = 0)

    (hfinJ : ∫⁻ t in Ω₂K, ∫⁻ k, ∫⁻ ζ, ‖((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ)‖ₑ * ‖((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) (algebraMap K (AdeleRing (𝓞 K) K) (η : K))) -
                (if Real.exp R < NumberField.AdelicHeight.adelicHeight L (diagOne t : AdelicGL2 (𝓞 L) L) then
                  ∫ r, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r ∂μK else 0))‖ₑ *
          ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L t)⁻¹
        ∂νZL ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ≠ ⊤)

    (hINV : ∀ (q : Kˣ) (t : (AdeleRing (𝓞 L) L)ˣ),
      (∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) * ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * (((t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L
            (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) q))⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L
            (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) q)) * (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L
            (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) q))⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) (algebraMap K (AdeleRing (𝓞 K) K) (η : K))) -
                (if Real.exp R < NumberField.AdelicHeight.adelicHeight L (diagOne (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L
            (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) q)) : AdelicGL2 (𝓞 L) L) then
                  ∫ r, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * (((t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L
            (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) q))⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L
            (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) q)) * (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L
            (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) q))⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r ∂μK else 0)) ∂νZL) *
          (((NumberField.TateGlobal.ideleNorm L (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L
            (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) q)))⁻¹ : ℝ) : ℂ)
        ∂(maximalCompactHaar L)) =
      ∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) * ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) (algebraMap K (AdeleRing (𝓞 K) K) (η : K))) -
                (if Real.exp R < NumberField.AdelicHeight.adelicHeight L (diagOne t : AdelicGL2 (𝓞 L) L) then
                  ∫ r, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r ∂μK else 0)) ∂νZL) *
          (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)
        ∂(maximalCompactHaar L))

    (hDIL : ∀ (t : (AdeleRing (𝓞 L) L)ˣ) (y : (AdeleRing (𝓞 K) K)ˣ),
      (∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) * ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * (((t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) * (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y)⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) (algebraMap K (AdeleRing (𝓞 K) K) (η : K))) -
                (if Real.exp R < NumberField.AdelicHeight.adelicHeight L (diagOne (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) : AdelicGL2 (𝓞 L) L) then
                  ∫ r, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * (((t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) * (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y)⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r ∂μK else 0)) ∂νZL) *
          (((NumberField.TateGlobal.ideleNorm L (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y))⁻¹ : ℝ) : ℂ)
        ∂(maximalCompactHaar L)) =
      (((NumberField.TateGlobal.ideleNorm L t)⁻¹ * (NumberField.TateGlobal.ideleNorm K y)⁻¹ : ℝ) : ℂ) *
        ∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) *
                ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)))
                    (algebraMap K (AdeleRing (𝓞 K) K) (η : K) * ((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))) -
                  (if Real.exp R < NumberField.AdelicHeight.adelicHeight L (diagOne (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) : AdelicGL2 (𝓞 L) L) then
                    ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ) * ∫ u, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) u ∂μK
                  else 0)) ∂νZL) ∂(maximalCompactHaar L))

    (hMEAS : @Measurable (AdeleRing (𝓞 L) L)ˣ ℂ (NumberField.Idele.ideleBorel L) _
      (fun t : (AdeleRing (𝓞 L) L)ˣ => ∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) * ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) (algebraMap K (AdeleRing (𝓞 K) K) (η : K))) -
                (if Real.exp R < NumberField.AdelicHeight.adelicHeight L (diagOne t : AdelicGL2 (𝓞 L) L) then
                  ∫ r, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r ∂μK else 0)) ∂νZL) *
          (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)
        ∂(maximalCompactHaar L))) :
    (∀ j : Fin n, IntegrableOn (fun y : (AdeleRing (𝓞 K) K)ˣ =>
        ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ)⁻¹ *
          (∫ t, ∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) *
                ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)))
                    (algebraMap K (AdeleRing (𝓞 K) K) (η : K) * ((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))) -
                  (if a j * Real.exp (b * R) < NumberField.TateGlobal.ideleNorm K y then
                    ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ) * ∫ u, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) u ∂μK
                  else 0)) ∂νZL) ∂(maximalCompactHaar L) ∂(τ j)))
        ΩK (NumberField.Idele.idelicHaar K)) ∧
    ∫ t in Ω₂K, ∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) * ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) (algebraMap K (AdeleRing (𝓞 K) K) (η : K))) -
                (if Real.exp R < NumberField.AdelicHeight.adelicHeight L (diagOne t : AdelicGL2 (𝓞 L) L) then
                  ∫ r, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r ∂μK else 0)) ∂νZL) *
          (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)
        ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) =
      ∑ j : Fin n, ((cτ.toReal * (c j)⁻¹ : ℝ) : ℂ) * ∫ y in ΩK,
          ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ)⁻¹ *
            (∫ t, ∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) *
                ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)))
                    (algebraMap K (AdeleRing (𝓞 K) K) (η : K) * ((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))) -
                  (if a j * Real.exp (b * R) < NumberField.TateGlobal.ideleNorm K y then
                    ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ) * ∫ u, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) u ∂μK
                  else 0)) ∂νZL) ∂(maximalCompactHaar L) ∂(τ j)) ∂(NumberField.Idele.idelicHaar K) := by
  refine G4CGlue.core K L Sτ n c τ cτ hcτ0 hcτT hcpos hlev hτfin hmeas hmul hτ0 hτ2 ΩK hΩK Ω₂K hΩ₂Km hΩ₂K
    (fun t : (AdeleRing (𝓞 L) L)ˣ => ∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) * ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) (algebraMap K (AdeleRing (𝓞 K) K) (η : K))) -
                (if Real.exp R < NumberField.AdelicHeight.adelicHeight L (diagOne t : AdelicGL2 (𝓞 L) L) then
                  ∫ r, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r ∂μK else 0)) ∂νZL) *
          (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)
        ∂(maximalCompactHaar L))
    (fun (t : (AdeleRing (𝓞 L) L)ˣ) (y : (AdeleRing (𝓞 K) K)ˣ) => ∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) *
                ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)))
                    (algebraMap K (AdeleRing (𝓞 K) K) (η : K) * ((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))) -
                  (if Real.exp R < NumberField.AdelicHeight.adelicHeight L (diagOne (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) : AdelicGL2 (𝓞 L) L) then
                    ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ) * ∫ u, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) u ∂μK
                  else 0)) ∂νZL) ∂(maximalCompactHaar L))
    (fun (j : Fin n) (t : (AdeleRing (𝓞 L) L)ˣ) (y : (AdeleRing (𝓞 K) K)ˣ) => ∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) *
                ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)))
                    (algebraMap K (AdeleRing (𝓞 K) K) (η : K) * ((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))) -
                  (if a j * Real.exp (b * R) < NumberField.TateGlobal.ideleNorm K y then
                    ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ) * ∫ u, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) u ∂μK
                  else 0)) ∂νZL) ∂(maximalCompactHaar L))
    hMEAS hINV hDIL ?_ ?_ ?_
  ·
    intro j t ht y
    simp only [hthr j t ht y]
  ·
    intro t ht
    simp only [hsupp t ht, tracePushforward_zero_fun, finsum_zero, integral_zero, ite_self, sub_self, mul_zero,
      zero_mul]
  ·
    refine ne_top_of_le_ne_top hfinJ (lintegral_mono fun t => ?_)
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun k => ?_)
    have hc : ‖(((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)‖ₑ =
        ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L t)⁻¹ := by
      rw [← ofReal_norm, Complex.norm_real,
        Real.norm_of_nonneg (inv_nonneg.2 (NumberField.TateGlobal.ideleNorm_pos t).le)]
    rw [enorm_mul, hc]
    refine le_trans (mul_le_mul_left (enorm_integral_le_lintegral_enorm _) _) ?_
    rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun ζ => ?_
    rw [enorm_mul]

end Concrete

end

end S_AutomorphicForm_TwistedBruhat_integrableOn_and_integral_unipotentFold_eq_sum_mul_setIntegral_rankOne_of_invariance_of_dilation_of_ne_top
end P2MW
export P2MW.S_AutomorphicForm_TwistedBruhat_integrableOn_and_integral_unipotentFold_eq_sum_mul_setIntegral_rankOne_of_invariance_of_dilation_of_ne_top (solution)
