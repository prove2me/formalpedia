-- Prove2me | solution 1 for AutomorphicForm.exists_forall_setIntegral_inv_ideleNorm_smul_integral_maximalCompact_mul_conj_constantTerm_eq_of_matched_paleyWiener
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/ed80c8ca-fd33-5935-bad1-6940d67e279f

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_AutomorphicForm_integrable_and_setIntegral_inv_ideleNorm_smul_integral_lineIntegral_mul_conj_eq_of_isInducedSection_of_eq_mul_normPowChar
import Theorems.Thm_AutomorphicForm_integrable_and_setIntegral_inv_ideleNorm_smul_integral_lineIntegral_mul_conj_eq_zero_of_isInducedSection_of_apply_ne
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_setIntegral_inv_ideleNorm_smul_integral_maximalCompact_mul_conj_constantTerm_eq_of_matched_paleyWiener
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

open scoped NNReal ENNReal

open AutomorphicForm

namespace TorusPairGlue

theorem exists_apply_ne_of_mul_eq {ι G M : Type*} [Group M] {μ ν : ι → G → M} {ξ : G → M} {P : G → Prop}
    (hμν : ∀ e x, μ e x * ν e x = ξ x)
    (hdist : ∀ e e' : ι, e ≠ e' → ∃ x, P x ∧ (μ e x ≠ μ e' x ∨ ν e x ≠ ν e' x)) :
    ∀ e e' : ι, e ≠ e' → ∃ x, P x ∧ μ e x ≠ μ e' x := by
  intro e e' hne
  obtain ⟨x, hx, h⟩ := hdist e e' hne
  rcases h with h | h
  · exact ⟨x, hx, h⟩
  · refine ⟨x, hx, fun hμ => h ?_⟩
    rw [eq_inv_mul_of_mul_eq (hμν e x), eq_inv_mul_of_mul_eq (hμν e' x), hμ]

variable {F : Type} [Field F] [NumberField F]

theorem ideleNorm_eq_one_of_mem_normOneIdeles {z : (AdeleRing (𝓞 F) F)ˣ}
    (hz : z ∈ NumberField.TateGlobal.normOneIdeles F) : NumberField.TateGlobal.ideleNorm F z = 1 := by
  have h : distribHaarChar (AdeleRing (𝓞 F) F) z = 1 := MonoidHom.mem_ker.mp hz
  simp [NumberField.TateGlobal.ideleNorm, h]

theorem normPowChar_apply_of_mem_normOneIdeles (τ : ℝ) {z : (AdeleRing (𝓞 F) F)ˣ}
    (hz : z ∈ NumberField.TateGlobal.normOneIdeles F) : NumberField.TateGlobal.normPowChar F τ z = 1 :=
  NumberField.TateGlobal.normPowChar_eq_one_of_ideleNorm_eq_one τ (ideleNorm_eq_one_of_mem_normOneIdeles hz)

theorem normPowChar_inv (τ : ℝ) :
    (NumberField.TateGlobal.normPowChar F τ)⁻¹ = NumberField.TateGlobal.normPowChar F (-τ) := by
  ext x
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, NumberField.TateGlobal.coe_normPowChar_apply,
    NumberField.TateGlobal.coe_normPowChar_apply, ← Complex.cpow_neg]
  congr 1
  push_cast
  ring

theorem sigmaFinite_idelicHaar (F : Type) [Field F] [NumberField F] :
    SigmaFinite (NumberField.Idele.idelicHaar F) := by
  haveI hLC : LocallyCompactSpace (AdeleRing (𝓞 F) F)ˣ := inferInstance
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F) := NumberField.AdeleRing.secondCountableTopology F
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F)ˣ := by
    haveI : SecondCountableTopology (AdeleRing (𝓞 F) F)ᵐᵒᵖ :=
      MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
    exact Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : SigmaCompactSpace (AdeleRing (𝓞 F) F)ˣ := sigmaCompactSpace_of_locallyCompact_secondCountable
  exact @MeasureTheory.Measure.IsHaarMeasure.sigmaFinite _ _ _ _ (NumberField.Idele.idelicHaar F)
    (NumberField.Idele.isHaarMeasure_idelicHaar F) _

end TorusPairGlue

theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (D : Set (AdeleRing (𝓞 K) K)ˣ) (_hDm : MeasurableSet D)
      (_hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D (NumberField.Idele.idelicHaar K))
      (V : ℝ≥0∞) (_hV0 : V ≠ 0) (_hVT : V ≠ ∞)
      (_hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
        ∫⁻ z in D, f (NumberField.TateGlobal.ideleNorm K z) ∂(NumberField.Idele.idelicHaar K) =
          V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹),
    ∃ C : ℝ, 0 < C ∧
    ∀
      (ι : Type) (b : ι → AdelicGL2 (𝓞 K) K → ℂ) (cls : ι → HeckeEigensystem K ℂ)
      (hb : ∀ i, cls i ∈ cuspClasses K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK ∧
          b i ∈ isotypicCuspSubmodule K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK (cls i) ⊓ archCutSubmodule K tysK)
      (hbn : ∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          b i g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 1)
      (hbo : ∀ i j, i ≠ j → ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          b i g * conj (b j g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (hbs : ∀ π ∈ cuspClasses K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK,
          {i | cls i = π}.Finite ∧
          Submodule.span ℂ (b '' {i | cls i = π}) = isotypicCuspSubmodule K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK π ⊓ archCutSubmodule K tysK)
      (hbc : ∀ φ : AdelicGL2 (𝓞 K) K → ℂ,
          IsSmoothCuspAutomorphicFnAt K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK φ →
          Continuous φ →
          (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).U N, φ (g * u) = φ g) →
          φ ∈ archCutSubmodule K tysK →
          (∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
              φ g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0) →
          φ =ᵐ[(adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)] 0)
      (ιE : Type) [Countable ιE]
      (μ ν : ιE → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μ e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (ν e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μ e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (ν e))
      (_hμc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ e z : ℂˣ) : ℂ))
      (_hνc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν e z : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιE) (z : (AdeleRing (𝓞 K) K)ˣ), μ e z * ν e z = ξK ⟨z, Subgroup.mem_top z⟩)
      (_hdist : ∀ e e' : ιE, e ≠ e' → ∃ z ∈ NumberField.TateGlobal.normOneIdeles K,
        μ e z ≠ μ e' z ∨ ν e z ≠ ν e' z)
      (nE : ιE → ℕ)
      (φE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφE : ∀ e j s, IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm s) (etaSnd (ν e) αm hαm s) (φE e j s))
      (_hφEK : ∀ e j s, IsArchKFinite K (φE e j s))
      (_hφEf : ∀ e j s, IsKfSmooth K (φE e j s))
      (_hφEjc : ∀ e j, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φE e j p.1 p.2))
      (_hφEhol : ∀ e j (g : AdelicGL2 (𝓞 K) K), Differentiable ℂ (fun s => φE e j s g))
      (_hφEKu : ∀ e j (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => φE e j s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφEflat : ∀ e j (s : ℂ) (k : adelicMaximalCompact K),
        φE e j s (k : AdelicGL2 (𝓞 K) K) = φE e j 0 (k : AdelicGL2 (𝓞 K) K))
      (_hφElev : ∀ e j (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φE e j s (g * u) = φE e j s g)
      (_hφEty : ∀ e j (s : ℂ), φE e j s ∈ archCutSubmodule K tysK)
      (_hφEon : ∀ e i j, ∫ k, φE e i 0 (k : AdelicGL2 (𝓞 K) K) * conj (φE e j 0 (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        if i = j then 1 else 0)
      (_hφEspan : ∀ (e : ιE) (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm ((t : ℂ) * Complex.I)) (etaSnd (ν e) αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK →
        φ₀ ∈ Submodule.span ℂ (Set.range fun j : Fin (nE e) => φE e j ((t : ℂ) * Complex.I)))
      (_hpairs : ∀ (μ' ν' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
        IsUnitaryChar (𝓞 K) K μ' → IsUnitaryChar (𝓞 K) K ν' →
        IsIdeleClassChar (𝓞 K) K μ' → IsIdeleClassChar (𝓞 K) K ν' →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ' z : ℂˣ) : ℂ)) →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν' z : ℂˣ) : ℂ)) →
        (∀ z : (AdeleRing (𝓞 K) K)ˣ, μ' z * ν' z = ξK ⟨z, Subgroup.mem_top z⟩) →
        ∀ (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst μ' αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν' αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK → φ₀ ≠ 0 →
        ∃ e : ιE, ∀ z ∈ NumberField.TateGlobal.normOneIdeles K, μ e z = μ' z ∧ ν e z = ν' z)
      (OE : ∀ e : ιE, Fin (nE e) → Set ℂ) (EE NE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hEE : ∀ (e : ιE) (j : Fin (nE e)),
      IsOpen (OE e j) ∧ IsPreconnected (OE e j) ∧ {s : ℂ | s.re = 0} ⊆ (OE e j) ∧ {s : ℂ | 1 / 2 < s.re} ⊆ (OE e j) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => EE e j s g) (OE e j)) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => NE e j s g) (OE e j)) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => EE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => NE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        EE e j s g = φE e j s g + ∑' ξ : K, φE e j s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        NE e j s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (φE e j s) g))
      (ιP : Type) [Fintype ιP]
      (μP νP : ιP → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μP e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (νP e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μP e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (νP e))
      (_hμc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((μP e x : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιP)
        (z : (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z),
        μP e (z : (AdeleRing (𝓞 K) K)ˣ) * νP e (z : (AdeleRing (𝓞 K) K)ˣ) = ξK z)
      (rP : ιP → ιP) (_hr : ∀ e, μP (rP e) = νP e ∧ νP (rP e) = μP e)
      (_hdist : ∀ e e' : ιP, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles K,
        μP e x ≠ μP e' x ∨ νP e x ≠ νP e' x)
      (ψf : ιP → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP e) αm hαm s) (etaSnd (νP e) αm hαm s) (ψf e s))
      (_hψjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf e p.1 p.2))
      (_hψhol : ∀ e g, Differentiable ℂ (fun s => ψf e s g))
      (_hνc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((νP e x : ℂˣ) : ℂ))
      (_hψdec : ∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (ψ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hψ : AutomorphicForm.IsSlabProfile K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK ψ)
      (_hψrep : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        ψ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (em : ιP → ιE) (τ : ιP → ℝ)
      (_hem : ∀ i : ιP, μP i = μ (em i) * NumberField.TateGlobal.normPowChar K (τ i) ∧
        νP i = ν (em i) * (NumberField.TateGlobal.normPowChar K (τ i))⁻¹)
      (_hNEind : ∀ (e : ιE) (j : Fin (nE e)) (t : ℝ),
        IsInducedSection (𝓞 K) K (etaFst (ν e) αm hαm (-((t : ℂ) * Complex.I)))
          (etaSnd (μ e) αm hαm (-((t : ℂ) * Complex.I))) (NE e j ((t : ℂ) * Complex.I))),
    (∀ (e : ιE) (j : Fin (nE e)) (t : ℝ),
      Integrable (fun p : (AdeleRing (𝓞 K) K)ˣ × adelicMaximalCompact K =>
          ψ (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K)) *
            conj ((fun g => φE e j ((t : ℂ) * Complex.I) g + ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) g)
              (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K))))
        ((((NumberField.Idele.idelicHaar K).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 K) K)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹))).prod (maximalCompactHaar K))) ∧
    (∀ (e : ιE), (∀ i : ιP, em i ≠ e) → ∀ (j : Fin (nE e)) (t : ℝ),
      ∫ y in D, (NumberField.TateGlobal.ideleNorm K y)⁻¹ •
            ∫ k, ψ (diagOne y * (k : AdelicGL2 (𝓞 K) K)) * conj ((fun g => φE e j ((t : ℂ) * Complex.I) g + ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) g) (diagOne y * (k : AdelicGL2 (𝓞 K) K))) ∂(maximalCompactHaar K)
          ∂(NumberField.Idele.idelicHaar K) = 0) ∧
    ∀ (i : ιP) (j : Fin (nE (em i))) (t : ℝ),
    let vol : ℂ := (((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)
    let tE : ℂ := (((t + τ i : ℝ) : ℂ)) * Complex.I
    ∫ y in D, (NumberField.TateGlobal.ideleNorm K y)⁻¹ •
            ∫ k, ψ (diagOne y * (k : AdelicGL2 (𝓞 K) K)) * conj ((fun g => φE (em i) j tE g + vol⁻¹ * NE (em i) j tE g) (diagOne y * (k : AdelicGL2 (𝓞 K) K))) ∂(maximalCompactHaar K)
          ∂(NumberField.Idele.idelicHaar K) =
        (C : ℂ) *
          ((∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j tE (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) +
            ∫ k, ψf (rP i) (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) * conj (vol⁻¹ * NE (em i) j tE (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) := by
  intro αm hαm D hDm hDF V hV0 hVT hV
  haveI : SigmaFinite (NumberField.Idele.idelicHaar K) := TorusPairGlue.sigmaFinite_idelicHaar K
  have hVpos : 0 < V.toReal := ENNReal.toReal_pos hV0 hVT
  refine ⟨V.toReal / 2, by positivity, ?_⟩
  intro ι b cls hb hbn hbo hbs hbc ιE _instC μ ν hμu hνu hμic hνic hμc hνc hμν hdistE nE φE hφE hφEK hφEf hφEjc hφEhol hφEKu hφEflat hφElev hφEty hφEon hφEspan hpairs OE EE NE hEE ιP _instF μP νP hμPu hνPu hμPic hνPic hμPc hμPν rP hr hdistP ψf hψf hψjc hψhol hνPc hψdec ψ hψ hψrep em τ hem hNEind
  classical
  refine ⟨?_, ?_, ?_⟩

  ·
    intro e j t
    obtain ⟨hO, hOc, hOax, hOhalf, hEa, hNa, hEjc, hNjc, hEser, hNser⟩ := hEE e j
    have htE : ((t : ℂ) * Complex.I) ∈ OE e j := hOax (by
      show (((t : ℂ)) * Complex.I).re = 0
      simp)
    have hφc : Continuous (fun g : AdelicGL2 (𝓞 K) K => φE e j ((t : ℂ) * Complex.I) g) :=
      (hφEjc e j).comp (continuous_const.prodMk continuous_id)
    have hNc : Continuous (fun g : AdelicGL2 (𝓞 K) K => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) g) :=
      continuous_const.mul (hNjc.comp_continuous (continuous_const.prodMk continuous_id) fun g => ⟨htE, Set.mem_univ g⟩)
    have hsmul : ∀ {χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {φ : AdelicGL2 (𝓞 K) K → ℂ} (a : ℂ),
        IsInducedSection (𝓞 K) K χ₁ χ₂ φ → IsInducedSection (𝓞 K) K χ₁ χ₂ (fun g => a * φ g) :=
      fun a h b hb g => by
        show a * _ = _ * (a * _)
        rw [h b hb g]
        ring
    have hcastN : (((-(t) : ℝ) : ℂ) * Complex.I) = -(((t : ℂ) * Complex.I)) := by
      show (((-(t) : ℝ) : ℂ) * Complex.I) = -(((t : ℂ)) * Complex.I)
      push_cast
      ring
    have hΦN : IsInducedSection (𝓞 K) K (etaFst (ν e) αm hαm (((-(t) : ℝ) : ℂ) * Complex.I))
        (etaSnd (μ e) αm hαm (((-(t) : ℝ) : ℂ) * Complex.I)) (fun g : AdelicGL2 (𝓞 K) K => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) g) := by
      rw [hcastN]
      exact hsmul ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ (hNEind e j (t))

    have sepP : ∀ a b : ιP, a ≠ b → ∃ z, z ∈ NumberField.TateGlobal.normOneIdeles K ∧ μP a z ≠ μP b z :=
      TorusPairGlue.exists_apply_ne_of_mul_eq (μ := fun a z => μP a z) (ν := fun a z => νP a z)
        (ξ := fun z => ξK ⟨z, Subgroup.mem_top z⟩) (P := fun z => z ∈ NumberField.TateGlobal.normOneIdeles K)
        (fun a z => hμPν a ⟨z, Subgroup.mem_top z⟩) (fun a b hab => by
          obtain ⟨z, hz, h⟩ := hdistP a b hab
          exact ⟨z, hz, h⟩)
    have sepE : ∀ a b : ιE, a ≠ b → ∃ z, z ∈ NumberField.TateGlobal.normOneIdeles K ∧ μ a z ≠ μ b z :=
      TorusPairGlue.exists_apply_ne_of_mul_eq (μ := fun a z => μ a z) (ν := fun a z => ν a z)
        (ξ := fun z => ξK ⟨z, Subgroup.mem_top z⟩) (P := fun z => z ∈ NumberField.TateGlobal.normOneIdeles K)
        (fun a z => hμν a z) (fun a b hab => by
          obtain ⟨z, hz, h⟩ := hdistE a b hab
          exact ⟨z, hz, h⟩)

    have hIφ : ∀ i' : ιP, Integrable (fun p : (AdeleRing (𝓞 K) K)ˣ × adelicMaximalCompact K =>
        (∫ t' : ℝ, ψf i' ((t' : ℂ) * Complex.I) (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K))) *
          conj ((fun g : AdelicGL2 (𝓞 K) K => φE e j ((t : ℂ) * Complex.I) g) (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K))))
        ((((NumberField.Idele.idelicHaar K).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 K) K)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹))).prod (maximalCompactHaar K)) := by
      intro i'
      by_cases h : em i' = e
      · exact (AutomorphicForm.integrable_and_setIntegral_inv_ideleNorm_smul_integral_lineIntegral_mul_conj_eq_of_isInducedSection_of_eq_mul_normPowChar K hαm D hDm hDF V hV0 hVT hV
          (μP i') (νP i') (hμPu i') (hνPu i') (hμPic i') (hνPic i') (hμPc i')
          (ψf i') (hψf i') (hψjc i') (hψhol i') (hψdec i') (μ e) (ν e) (hμu e) (hμic e) (t) (fun g : AdelicGL2 (𝓞 K) K => φE e j ((t : ℂ) * Complex.I) g) (hφE e j ((t : ℂ) * Complex.I)) hφc (τ i') (by rw [← h]; exact (hem i').1)).1
      · obtain ⟨z, hz, hne⟩ := sepE (em i') e h
        have hne' : μP i' z ≠ μ e z := by
          rwa [(hem i').1, MonoidHom.mul_apply, TorusPairGlue.normPowChar_apply_of_mem_normOneIdeles _ hz, mul_one]
        exact (AutomorphicForm.integrable_and_setIntegral_inv_ideleNorm_smul_integral_lineIntegral_mul_conj_eq_zero_of_isInducedSection_of_apply_ne K hαm D hDm hDF V hV0 hVT hV
          (μP i') (νP i') (hμPu i') (hνPu i') (hμPic i') (hνPic i') (hμPc i')
          (ψf i') (hψf i') (hψjc i') (hψhol i') (hψdec i') (μ e) (ν e) (hμu e) (hμic e) (t) (fun g : AdelicGL2 (𝓞 K) K => φE e j ((t : ℂ) * Complex.I) g) (hφE e j ((t : ℂ) * Complex.I)) hφc z hz hne').1
    have hIN : ∀ i' : ιP, Integrable (fun p : (AdeleRing (𝓞 K) K)ˣ × adelicMaximalCompact K =>
        (∫ t' : ℝ, ψf i' ((t' : ℂ) * Complex.I) (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K))) *
          conj ((fun g : AdelicGL2 (𝓞 K) K => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) g) (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K))))
        ((((NumberField.Idele.idelicHaar K).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 K) K)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹))).prod (maximalCompactHaar K)) := by
      intro i'
      by_cases h : em (rP i') = e
      · have hmatch : μP i' = ν e * NumberField.TateGlobal.normPowChar K (-τ (rP i')) := by
          rw [← TorusPairGlue.normPowChar_inv]
          refine MonoidHom.ext fun z => ?_
          rw [MonoidHom.mul_apply, MonoidHom.inv_apply, eq_mul_inv_iff_mul_eq]
          have h4 : μP i' z * νP i' z = ξK ⟨z, Subgroup.mem_top z⟩ := hμPν i' ⟨z, Subgroup.mem_top z⟩
          have h5 : μ e z * ν e z = ξK ⟨z, Subgroup.mem_top z⟩ := hμν e z
          have h3 : νP i' z = μ e z * NumberField.TateGlobal.normPowChar K (τ (rP i')) z := by
            rw [← (hr i').1, (hem (rP i')).1, h, MonoidHom.mul_apply]
          have h6 : μ e z * (μP i' z * NumberField.TateGlobal.normPowChar K (τ (rP i')) z) = μ e z * ν e z := by
            rw [mul_left_comm, ← h3, h4, h5]
          exact mul_left_cancel h6
        exact (AutomorphicForm.integrable_and_setIntegral_inv_ideleNorm_smul_integral_lineIntegral_mul_conj_eq_of_isInducedSection_of_eq_mul_normPowChar K hαm D hDm hDF V hV0 hVT hV
          (μP i') (νP i') (hμPu i') (hνPu i') (hμPic i') (hνPic i') (hμPc i')
          (ψf i') (hψf i') (hψjc i') (hψhol i') (hψdec i') (ν e) (μ e) (hνu e) (hνic e) (-(t)) (fun g : AdelicGL2 (𝓞 K) K => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) g) (hΦN) hNc (-τ (rP i')) (hmatch)).1
      · have hsep : ∃ z, z ∈ NumberField.TateGlobal.normOneIdeles K ∧ μP i' z ≠ ν e z := by
          by_contra hall
          push Not at hall
          apply h
          by_contra hne
          obtain ⟨z, hz, hμz⟩ := sepE (em (rP i')) e hne
          apply hμz
          have h1 : μP i' z = ν e z := by
            have := hall z
            tauto
          have h2 : μ (em (rP i')) z = μP (rP i') z := by
            rw [(hem (rP i')).1, MonoidHom.mul_apply, TorusPairGlue.normPowChar_apply_of_mem_normOneIdeles _ hz, mul_one]
          have h3 : μP (rP i') z = νP i' z := by rw [(hr i').1]
          have h4 : μP i' z * νP i' z = ξK ⟨z, Subgroup.mem_top z⟩ := hμPν i' ⟨z, Subgroup.mem_top z⟩
          have h5 : μ e z * ν e z = ξK ⟨z, Subgroup.mem_top z⟩ := hμν e z
          rw [h2, h3]
          rw [h1] at h4
          have h6 : ν e z * νP i' z = ν e z * μ e z := by rw [h4, ← h5, mul_comm]
          exact mul_left_cancel h6
        obtain ⟨z, hz, hne'⟩ := hsep
        exact (AutomorphicForm.integrable_and_setIntegral_inv_ideleNorm_smul_integral_lineIntegral_mul_conj_eq_zero_of_isInducedSection_of_apply_ne K hαm D hDm hDF V hV0 hVT hV
          (μP i') (νP i') (hμPu i') (hνPu i') (hμPic i') (hνPic i') (hμPc i')
          (ψf i') (hψf i') (hψjc i') (hψhol i') (hψdec i') (ν e) (μ e) (hνu e) (hνic e) (-(t)) (fun g : AdelicGL2 (𝓞 K) K => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) g) (hΦN) hNc z hz hne').1

    have hpt : (fun p : (AdeleRing (𝓞 K) K)ˣ × adelicMaximalCompact K =>
          ψ (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K)) *
            conj ((fun g : AdelicGL2 (𝓞 K) K => φE e j ((t : ℂ) * Complex.I) g + ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) g)
              (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K)))) =
        fun p => (((4 * Real.pi)⁻¹ : ℝ) : ℂ) * ∑ i' : ιP,
          ((∫ t' : ℝ, ψf i' ((t' : ℂ) * Complex.I) (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K))) *
              conj ((fun g : AdelicGL2 (𝓞 K) K => φE e j ((t : ℂ) * Complex.I) g) (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K))) +
           (∫ t' : ℝ, ψf i' ((t' : ℂ) * Complex.I) (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K))) *
              conj ((fun g : AdelicGL2 (𝓞 K) K => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) g) (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K)))) := by
      funext p
      rw [hψrep 0 (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K))]
      simp only [Complex.ofReal_zero, zero_add, Finset.sum_mul, Finset.mul_sum, map_add]
      refine Finset.sum_congr rfl fun i' _ => ?_
      ring
    have hIψ : Integrable (fun p : (AdeleRing (𝓞 K) K)ˣ × adelicMaximalCompact K =>
          ψ (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K)) *
            conj ((fun g : AdelicGL2 (𝓞 K) K => φE e j ((t : ℂ) * Complex.I) g + ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) g)
              (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K)))) ((((NumberField.Idele.idelicHaar K).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 K) K)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹))).prod (maximalCompactHaar K)) := by
      rw [hpt]
      exact (integrable_finsetSum _ fun i' _ => (hIφ i').add (hIN i')).const_mul _

    have key : ∀ (F : (AdeleRing (𝓞 K) K)ˣ × adelicMaximalCompact K → ℂ), Integrable F ((((NumberField.Idele.idelicHaar K).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 K) K)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹))).prod (maximalCompactHaar K)) →
        (∫ y in D, (NumberField.TateGlobal.ideleNorm K y)⁻¹ • ∫ k, F (y, k) ∂(maximalCompactHaar K)
          ∂(NumberField.Idele.idelicHaar K)) = ∫ p, F p ∂((((NumberField.Idele.idelicHaar K).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 K) K)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹))).prod (maximalCompactHaar K)) := by
      intro F hF
      rw [MeasureTheory.integral_prod F hF,
        integral_withDensity_eq_integral_toReal_smul
          ((NumberField.TateGlobal.continuous_ideleNorm K).measurable.fun_inv.ennreal_ofReal)
          (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      refine setIntegral_congr_fun hDm fun y _ => ?_
      rw [ENNReal.toReal_ofReal (inv_nonneg.2 (NumberField.TateGlobal.ideleNorm_pos (F := K) y).le)]
    exact hIψ

  ·
    intro e he j t
    obtain ⟨hO, hOc, hOax, hOhalf, hEa, hNa, hEjc, hNjc, hEser, hNser⟩ := hEE e j
    have htE : ((t : ℂ) * Complex.I) ∈ OE e j := hOax (by
      show (((t : ℂ)) * Complex.I).re = 0
      simp)
    have hφc : Continuous (fun g : AdelicGL2 (𝓞 K) K => φE e j ((t : ℂ) * Complex.I) g) :=
      (hφEjc e j).comp (continuous_const.prodMk continuous_id)
    have hNc : Continuous (fun g : AdelicGL2 (𝓞 K) K => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) g) :=
      continuous_const.mul (hNjc.comp_continuous (continuous_const.prodMk continuous_id) fun g => ⟨htE, Set.mem_univ g⟩)
    have hsmul : ∀ {χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {φ : AdelicGL2 (𝓞 K) K → ℂ} (a : ℂ),
        IsInducedSection (𝓞 K) K χ₁ χ₂ φ → IsInducedSection (𝓞 K) K χ₁ χ₂ (fun g => a * φ g) :=
      fun a h b hb g => by
        show a * _ = _ * (a * _)
        rw [h b hb g]
        ring
    have hcastN : (((-(t) : ℝ) : ℂ) * Complex.I) = -(((t : ℂ) * Complex.I)) := by
      show (((-(t) : ℝ) : ℂ) * Complex.I) = -(((t : ℂ)) * Complex.I)
      push_cast
      ring
    have hΦN : IsInducedSection (𝓞 K) K (etaFst (ν e) αm hαm (((-(t) : ℝ) : ℂ) * Complex.I))
        (etaSnd (μ e) αm hαm (((-(t) : ℝ) : ℂ) * Complex.I)) (fun g : AdelicGL2 (𝓞 K) K => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) g) := by
      rw [hcastN]
      exact hsmul ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ (hNEind e j (t))

    have sepP : ∀ a b : ιP, a ≠ b → ∃ z, z ∈ NumberField.TateGlobal.normOneIdeles K ∧ μP a z ≠ μP b z :=
      TorusPairGlue.exists_apply_ne_of_mul_eq (μ := fun a z => μP a z) (ν := fun a z => νP a z)
        (ξ := fun z => ξK ⟨z, Subgroup.mem_top z⟩) (P := fun z => z ∈ NumberField.TateGlobal.normOneIdeles K)
        (fun a z => hμPν a ⟨z, Subgroup.mem_top z⟩) (fun a b hab => by
          obtain ⟨z, hz, h⟩ := hdistP a b hab
          exact ⟨z, hz, h⟩)
    have sepE : ∀ a b : ιE, a ≠ b → ∃ z, z ∈ NumberField.TateGlobal.normOneIdeles K ∧ μ a z ≠ μ b z :=
      TorusPairGlue.exists_apply_ne_of_mul_eq (μ := fun a z => μ a z) (ν := fun a z => ν a z)
        (ξ := fun z => ξK ⟨z, Subgroup.mem_top z⟩) (P := fun z => z ∈ NumberField.TateGlobal.normOneIdeles K)
        (fun a z => hμν a z) (fun a b hab => by
          obtain ⟨z, hz, h⟩ := hdistE a b hab
          exact ⟨z, hz, h⟩)

    have hIφ : ∀ i' : ιP, Integrable (fun p : (AdeleRing (𝓞 K) K)ˣ × adelicMaximalCompact K =>
        (∫ t' : ℝ, ψf i' ((t' : ℂ) * Complex.I) (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K))) *
          conj ((fun g : AdelicGL2 (𝓞 K) K => φE e j ((t : ℂ) * Complex.I) g) (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K))))
        ((((NumberField.Idele.idelicHaar K).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 K) K)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹))).prod (maximalCompactHaar K)) := by
      intro i'
      by_cases h : em i' = e
      · exact (AutomorphicForm.integrable_and_setIntegral_inv_ideleNorm_smul_integral_lineIntegral_mul_conj_eq_of_isInducedSection_of_eq_mul_normPowChar K hαm D hDm hDF V hV0 hVT hV
          (μP i') (νP i') (hμPu i') (hνPu i') (hμPic i') (hνPic i') (hμPc i')
          (ψf i') (hψf i') (hψjc i') (hψhol i') (hψdec i') (μ e) (ν e) (hμu e) (hμic e) (t) (fun g : AdelicGL2 (𝓞 K) K => φE e j ((t : ℂ) * Complex.I) g) (hφE e j ((t : ℂ) * Complex.I)) hφc (τ i') (by rw [← h]; exact (hem i').1)).1
      · obtain ⟨z, hz, hne⟩ := sepE (em i') e h
        have hne' : μP i' z ≠ μ e z := by
          rwa [(hem i').1, MonoidHom.mul_apply, TorusPairGlue.normPowChar_apply_of_mem_normOneIdeles _ hz, mul_one]
        exact (AutomorphicForm.integrable_and_setIntegral_inv_ideleNorm_smul_integral_lineIntegral_mul_conj_eq_zero_of_isInducedSection_of_apply_ne K hαm D hDm hDF V hV0 hVT hV
          (μP i') (νP i') (hμPu i') (hνPu i') (hμPic i') (hνPic i') (hμPc i')
          (ψf i') (hψf i') (hψjc i') (hψhol i') (hψdec i') (μ e) (ν e) (hμu e) (hμic e) (t) (fun g : AdelicGL2 (𝓞 K) K => φE e j ((t : ℂ) * Complex.I) g) (hφE e j ((t : ℂ) * Complex.I)) hφc z hz hne').1
    have hIN : ∀ i' : ιP, Integrable (fun p : (AdeleRing (𝓞 K) K)ˣ × adelicMaximalCompact K =>
        (∫ t' : ℝ, ψf i' ((t' : ℂ) * Complex.I) (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K))) *
          conj ((fun g : AdelicGL2 (𝓞 K) K => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) g) (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K))))
        ((((NumberField.Idele.idelicHaar K).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 K) K)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹))).prod (maximalCompactHaar K)) := by
      intro i'
      by_cases h : em (rP i') = e
      · have hmatch : μP i' = ν e * NumberField.TateGlobal.normPowChar K (-τ (rP i')) := by
          rw [← TorusPairGlue.normPowChar_inv]
          refine MonoidHom.ext fun z => ?_
          rw [MonoidHom.mul_apply, MonoidHom.inv_apply, eq_mul_inv_iff_mul_eq]
          have h4 : μP i' z * νP i' z = ξK ⟨z, Subgroup.mem_top z⟩ := hμPν i' ⟨z, Subgroup.mem_top z⟩
          have h5 : μ e z * ν e z = ξK ⟨z, Subgroup.mem_top z⟩ := hμν e z
          have h3 : νP i' z = μ e z * NumberField.TateGlobal.normPowChar K (τ (rP i')) z := by
            rw [← (hr i').1, (hem (rP i')).1, h, MonoidHom.mul_apply]
          have h6 : μ e z * (μP i' z * NumberField.TateGlobal.normPowChar K (τ (rP i')) z) = μ e z * ν e z := by
            rw [mul_left_comm, ← h3, h4, h5]
          exact mul_left_cancel h6
        exact (AutomorphicForm.integrable_and_setIntegral_inv_ideleNorm_smul_integral_lineIntegral_mul_conj_eq_of_isInducedSection_of_eq_mul_normPowChar K hαm D hDm hDF V hV0 hVT hV
          (μP i') (νP i') (hμPu i') (hνPu i') (hμPic i') (hνPic i') (hμPc i')
          (ψf i') (hψf i') (hψjc i') (hψhol i') (hψdec i') (ν e) (μ e) (hνu e) (hνic e) (-(t)) (fun g : AdelicGL2 (𝓞 K) K => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) g) (hΦN) hNc (-τ (rP i')) (hmatch)).1
      · have hsep : ∃ z, z ∈ NumberField.TateGlobal.normOneIdeles K ∧ μP i' z ≠ ν e z := by
          by_contra hall
          push Not at hall
          apply h
          by_contra hne
          obtain ⟨z, hz, hμz⟩ := sepE (em (rP i')) e hne
          apply hμz
          have h1 : μP i' z = ν e z := by
            have := hall z
            tauto
          have h2 : μ (em (rP i')) z = μP (rP i') z := by
            rw [(hem (rP i')).1, MonoidHom.mul_apply, TorusPairGlue.normPowChar_apply_of_mem_normOneIdeles _ hz, mul_one]
          have h3 : μP (rP i') z = νP i' z := by rw [(hr i').1]
          have h4 : μP i' z * νP i' z = ξK ⟨z, Subgroup.mem_top z⟩ := hμPν i' ⟨z, Subgroup.mem_top z⟩
          have h5 : μ e z * ν e z = ξK ⟨z, Subgroup.mem_top z⟩ := hμν e z
          rw [h2, h3]
          rw [h1] at h4
          have h6 : ν e z * νP i' z = ν e z * μ e z := by rw [h4, ← h5, mul_comm]
          exact mul_left_cancel h6
        obtain ⟨z, hz, hne'⟩ := hsep
        exact (AutomorphicForm.integrable_and_setIntegral_inv_ideleNorm_smul_integral_lineIntegral_mul_conj_eq_zero_of_isInducedSection_of_apply_ne K hαm D hDm hDF V hV0 hVT hV
          (μP i') (νP i') (hμPu i') (hνPu i') (hμPic i') (hνPic i') (hμPc i')
          (ψf i') (hψf i') (hψjc i') (hψhol i') (hψdec i') (ν e) (μ e) (hνu e) (hνic e) (-(t)) (fun g : AdelicGL2 (𝓞 K) K => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) g) (hΦN) hNc z hz hne').1

    have hpt : (fun p : (AdeleRing (𝓞 K) K)ˣ × adelicMaximalCompact K =>
          ψ (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K)) *
            conj ((fun g : AdelicGL2 (𝓞 K) K => φE e j ((t : ℂ) * Complex.I) g + ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) g)
              (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K)))) =
        fun p => (((4 * Real.pi)⁻¹ : ℝ) : ℂ) * ∑ i' : ιP,
          ((∫ t' : ℝ, ψf i' ((t' : ℂ) * Complex.I) (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K))) *
              conj ((fun g : AdelicGL2 (𝓞 K) K => φE e j ((t : ℂ) * Complex.I) g) (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K))) +
           (∫ t' : ℝ, ψf i' ((t' : ℂ) * Complex.I) (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K))) *
              conj ((fun g : AdelicGL2 (𝓞 K) K => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) g) (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K)))) := by
      funext p
      rw [hψrep 0 (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K))]
      simp only [Complex.ofReal_zero, zero_add, Finset.sum_mul, Finset.mul_sum, map_add]
      refine Finset.sum_congr rfl fun i' _ => ?_
      ring
    have hIψ : Integrable (fun p : (AdeleRing (𝓞 K) K)ˣ × adelicMaximalCompact K =>
          ψ (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K)) *
            conj ((fun g : AdelicGL2 (𝓞 K) K => φE e j ((t : ℂ) * Complex.I) g + ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) g)
              (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K)))) ((((NumberField.Idele.idelicHaar K).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 K) K)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹))).prod (maximalCompactHaar K)) := by
      rw [hpt]
      exact (integrable_finsetSum _ fun i' _ => (hIφ i').add (hIN i')).const_mul _

    have key : ∀ (F : (AdeleRing (𝓞 K) K)ˣ × adelicMaximalCompact K → ℂ), Integrable F ((((NumberField.Idele.idelicHaar K).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 K) K)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹))).prod (maximalCompactHaar K)) →
        (∫ y in D, (NumberField.TateGlobal.ideleNorm K y)⁻¹ • ∫ k, F (y, k) ∂(maximalCompactHaar K)
          ∂(NumberField.Idele.idelicHaar K)) = ∫ p, F p ∂((((NumberField.Idele.idelicHaar K).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 K) K)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹))).prod (maximalCompactHaar K)) := by
      intro F hF
      rw [MeasureTheory.integral_prod F hF,
        integral_withDensity_eq_integral_toReal_smul
          ((NumberField.TateGlobal.continuous_ideleNorm K).measurable.fun_inv.ennreal_ofReal)
          (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      refine setIntegral_congr_fun hDm fun y _ => ?_
      rw [ENNReal.toReal_ofReal (inv_nonneg.2 (NumberField.TateGlobal.ideleNorm_pos (F := K) y).le)]
    have hsplit :
        (∫ y in D, (NumberField.TateGlobal.ideleNorm K y)⁻¹ •
            ∫ k, ψ (diagOne y * (k : AdelicGL2 (𝓞 K) K)) * conj ((fun g => φE e j ((t : ℂ) * Complex.I) g + ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) g) (diagOne y * (k : AdelicGL2 (𝓞 K) K))) ∂(maximalCompactHaar K)
          ∂(NumberField.Idele.idelicHaar K)) =
        (((4 * Real.pi)⁻¹ : ℝ) : ℂ) * ∑ i' : ιP,
          ((∫ y in D, (NumberField.TateGlobal.ideleNorm K y)⁻¹ •
              ∫ k, (∫ t' : ℝ, ψf i' ((t' : ℂ) * Complex.I) (diagOne y * (k : AdelicGL2 (𝓞 K) K))) *
                  conj ((fun g => φE e j ((t : ℂ) * Complex.I) g) (diagOne y * (k : AdelicGL2 (𝓞 K) K))) ∂(maximalCompactHaar K)
            ∂(NumberField.Idele.idelicHaar K)) +
           (∫ y in D, (NumberField.TateGlobal.ideleNorm K y)⁻¹ •
              ∫ k, (∫ t' : ℝ, ψf i' ((t' : ℂ) * Complex.I) (diagOne y * (k : AdelicGL2 (𝓞 K) K))) *
                  conj ((fun g => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) g) (diagOne y * (k : AdelicGL2 (𝓞 K) K))) ∂(maximalCompactHaar K)
            ∂(NumberField.Idele.idelicHaar K))) := by
      rw [key _ hIψ, hpt, integral_const_mul, integral_finsetSum Finset.univ fun i' _ =>
        (show Integrable (fun p : (AdeleRing (𝓞 K) K)ˣ × adelicMaximalCompact K => _ + _) _ from (hIφ i').add (hIN i'))]
      congr 1
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [integral_add (hIφ i') (hIN i'), key _ (hIφ i'), key _ (hIN i')]

    have hφ : ∀ i' : ιP, (∫ y in D, (NumberField.TateGlobal.ideleNorm K y)⁻¹ •
              ∫ k, (∫ t' : ℝ, ψf i' ((t' : ℂ) * Complex.I) (diagOne y * (k : AdelicGL2 (𝓞 K) K))) *
                  conj ((fun g => φE e j ((t : ℂ) * Complex.I) g) (diagOne y * (k : AdelicGL2 (𝓞 K) K))) ∂(maximalCompactHaar K)
            ∂(NumberField.Idele.idelicHaar K)) = 0 := by
      intro i'
      obtain ⟨z, hz, hne⟩ := sepE (em i') e (he i')
      have hne' : μP i' z ≠ μ e z := by
        rwa [(hem i').1, MonoidHom.mul_apply, TorusPairGlue.normPowChar_apply_of_mem_normOneIdeles _ hz, mul_one]
      exact (AutomorphicForm.integrable_and_setIntegral_inv_ideleNorm_smul_integral_lineIntegral_mul_conj_eq_zero_of_isInducedSection_of_apply_ne K hαm D hDm hDF V hV0 hVT hV
          (μP i') (νP i') (hμPu i') (hνPu i') (hμPic i') (hνPic i') (hμPc i')
          (ψf i') (hψf i') (hψjc i') (hψhol i') (hψdec i') (μ e) (ν e) (hμu e) (hμic e) (t) (fun g : AdelicGL2 (𝓞 K) K => φE e j ((t : ℂ) * Complex.I) g) (hφE e j ((t : ℂ) * Complex.I)) hφc z hz hne').2
    have hN : ∀ i' : ιP, (∫ y in D, (NumberField.TateGlobal.ideleNorm K y)⁻¹ •
              ∫ k, (∫ t' : ℝ, ψf i' ((t' : ℂ) * Complex.I) (diagOne y * (k : AdelicGL2 (𝓞 K) K))) *
                  conj ((fun g => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) g) (diagOne y * (k : AdelicGL2 (𝓞 K) K))) ∂(maximalCompactHaar K)
            ∂(NumberField.Idele.idelicHaar K)) = 0 := by
      intro i'
      have hsep : ∃ z, z ∈ NumberField.TateGlobal.normOneIdeles K ∧ μP i' z ≠ ν e z := by
        by_contra hall
        push Not at hall
        apply he (rP i')
        by_contra hne
        obtain ⟨z, hz, hμz⟩ := sepE (em (rP i')) e hne
        apply hμz
        have h1 : μP i' z = ν e z := by
          have := hall z
          tauto
        have h2 : μ (em (rP i')) z = μP (rP i') z := by
          rw [(hem (rP i')).1, MonoidHom.mul_apply, TorusPairGlue.normPowChar_apply_of_mem_normOneIdeles _ hz, mul_one]
        have h3 : μP (rP i') z = νP i' z := by rw [(hr i').1]
        have h4 : μP i' z * νP i' z = ξK ⟨z, Subgroup.mem_top z⟩ := hμPν i' ⟨z, Subgroup.mem_top z⟩
        have h5 : μ e z * ν e z = ξK ⟨z, Subgroup.mem_top z⟩ := hμν e z
        rw [h2, h3]
        rw [h1] at h4
        have h6 : ν e z * νP i' z = ν e z * μ e z := by rw [h4, ← h5, mul_comm]
        exact mul_left_cancel h6
      obtain ⟨z, hz, hne'⟩ := hsep
      exact (AutomorphicForm.integrable_and_setIntegral_inv_ideleNorm_smul_integral_lineIntegral_mul_conj_eq_zero_of_isInducedSection_of_apply_ne K hαm D hDm hDF V hV0 hVT hV
          (μP i') (νP i') (hμPu i') (hνPu i') (hμPic i') (hνPic i') (hμPc i')
          (ψf i') (hψf i') (hψjc i') (hψhol i') (hψdec i') (ν e) (μ e) (hνu e) (hνic e) (-t) (fun g : AdelicGL2 (𝓞 K) K => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) g) (hΦN) hNc z hz hne').2
    rw [hsplit]
    simp_rw [hφ, hN]
    simp

  ·
    intro i j t vol tE
    obtain ⟨hO, hOc, hOax, hOhalf, hEa, hNa, hEjc, hNjc, hEser, hNser⟩ := hEE (em i) j
    have htE : tE ∈ OE (em i) j := hOax (by
      show ((((t + τ i : ℝ) : ℂ)) * Complex.I).re = 0
      simp)
    have hφc : Continuous (fun g : AdelicGL2 (𝓞 K) K => φE (em i) j tE g) :=
      (hφEjc (em i) j).comp (continuous_const.prodMk continuous_id)
    have hNc : Continuous (fun g : AdelicGL2 (𝓞 K) K => vol⁻¹ * NE (em i) j tE g) :=
      continuous_const.mul (hNjc.comp_continuous (continuous_const.prodMk continuous_id) fun g => ⟨htE, Set.mem_univ g⟩)
    have hsmul : ∀ {χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {φ : AdelicGL2 (𝓞 K) K → ℂ} (a : ℂ),
        IsInducedSection (𝓞 K) K χ₁ χ₂ φ → IsInducedSection (𝓞 K) K χ₁ χ₂ (fun g => a * φ g) :=
      fun a h b hb g => by
        show a * _ = _ * (a * _)
        rw [h b hb g]
        ring
    have hcastN : (((-(t + τ i) : ℝ) : ℂ) * Complex.I) = -(tE) := by
      show (((-(t + τ i) : ℝ) : ℂ) * Complex.I) = -((((t + τ i : ℝ) : ℂ)) * Complex.I)
      push_cast
      ring
    have hΦN : IsInducedSection (𝓞 K) K (etaFst (ν (em i)) αm hαm (((-(t + τ i) : ℝ) : ℂ) * Complex.I))
        (etaSnd (μ (em i)) αm hαm (((-(t + τ i) : ℝ) : ℂ) * Complex.I)) (fun g : AdelicGL2 (𝓞 K) K => vol⁻¹ * NE (em i) j tE g) := by
      rw [hcastN]
      exact hsmul vol⁻¹ (hNEind (em i) j (t + τ i))

    have sepP : ∀ a b : ιP, a ≠ b → ∃ z, z ∈ NumberField.TateGlobal.normOneIdeles K ∧ μP a z ≠ μP b z :=
      TorusPairGlue.exists_apply_ne_of_mul_eq (μ := fun a z => μP a z) (ν := fun a z => νP a z)
        (ξ := fun z => ξK ⟨z, Subgroup.mem_top z⟩) (P := fun z => z ∈ NumberField.TateGlobal.normOneIdeles K)
        (fun a z => hμPν a ⟨z, Subgroup.mem_top z⟩) (fun a b hab => by
          obtain ⟨z, hz, h⟩ := hdistP a b hab
          exact ⟨z, hz, h⟩)
    have sepE : ∀ a b : ιE, a ≠ b → ∃ z, z ∈ NumberField.TateGlobal.normOneIdeles K ∧ μ a z ≠ μ b z :=
      TorusPairGlue.exists_apply_ne_of_mul_eq (μ := fun a z => μ a z) (ν := fun a z => ν a z)
        (ξ := fun z => ξK ⟨z, Subgroup.mem_top z⟩) (P := fun z => z ∈ NumberField.TateGlobal.normOneIdeles K)
        (fun a z => hμν a z) (fun a b hab => by
          obtain ⟨z, hz, h⟩ := hdistE a b hab
          exact ⟨z, hz, h⟩)

    have hIφ : ∀ i' : ιP, Integrable (fun p : (AdeleRing (𝓞 K) K)ˣ × adelicMaximalCompact K =>
        (∫ t' : ℝ, ψf i' ((t' : ℂ) * Complex.I) (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K))) *
          conj ((fun g : AdelicGL2 (𝓞 K) K => φE (em i) j tE g) (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K))))
        ((((NumberField.Idele.idelicHaar K).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 K) K)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹))).prod (maximalCompactHaar K)) := by
      intro i'
      by_cases h : em i' = (em i)
      · exact (AutomorphicForm.integrable_and_setIntegral_inv_ideleNorm_smul_integral_lineIntegral_mul_conj_eq_of_isInducedSection_of_eq_mul_normPowChar K hαm D hDm hDF V hV0 hVT hV
          (μP i') (νP i') (hμPu i') (hνPu i') (hμPic i') (hνPic i') (hμPc i')
          (ψf i') (hψf i') (hψjc i') (hψhol i') (hψdec i') (μ (em i)) (ν (em i)) (hμu (em i)) (hμic (em i)) (t + τ i) (fun g : AdelicGL2 (𝓞 K) K => φE (em i) j tE g) (hφE (em i) j tE) hφc (τ i') (by rw [← h]; exact (hem i').1)).1
      · obtain ⟨z, hz, hne⟩ := sepE (em i') (em i) h
        have hne' : μP i' z ≠ μ (em i) z := by
          rwa [(hem i').1, MonoidHom.mul_apply, TorusPairGlue.normPowChar_apply_of_mem_normOneIdeles _ hz, mul_one]
        exact (AutomorphicForm.integrable_and_setIntegral_inv_ideleNorm_smul_integral_lineIntegral_mul_conj_eq_zero_of_isInducedSection_of_apply_ne K hαm D hDm hDF V hV0 hVT hV
          (μP i') (νP i') (hμPu i') (hνPu i') (hμPic i') (hνPic i') (hμPc i')
          (ψf i') (hψf i') (hψjc i') (hψhol i') (hψdec i') (μ (em i)) (ν (em i)) (hμu (em i)) (hμic (em i)) (t + τ i) (fun g : AdelicGL2 (𝓞 K) K => φE (em i) j tE g) (hφE (em i) j tE) hφc z hz hne').1
    have hIN : ∀ i' : ιP, Integrable (fun p : (AdeleRing (𝓞 K) K)ˣ × adelicMaximalCompact K =>
        (∫ t' : ℝ, ψf i' ((t' : ℂ) * Complex.I) (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K))) *
          conj ((fun g : AdelicGL2 (𝓞 K) K => vol⁻¹ * NE (em i) j tE g) (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K))))
        ((((NumberField.Idele.idelicHaar K).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 K) K)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹))).prod (maximalCompactHaar K)) := by
      intro i'
      by_cases h : em (rP i') = (em i)
      · have hmatch : μP i' = ν (em i) * NumberField.TateGlobal.normPowChar K (-τ (rP i')) := by
          rw [← TorusPairGlue.normPowChar_inv]
          refine MonoidHom.ext fun z => ?_
          rw [MonoidHom.mul_apply, MonoidHom.inv_apply, eq_mul_inv_iff_mul_eq]
          have h4 : μP i' z * νP i' z = ξK ⟨z, Subgroup.mem_top z⟩ := hμPν i' ⟨z, Subgroup.mem_top z⟩
          have h5 : μ (em i) z * ν (em i) z = ξK ⟨z, Subgroup.mem_top z⟩ := hμν (em i) z
          have h3 : νP i' z = μ (em i) z * NumberField.TateGlobal.normPowChar K (τ (rP i')) z := by
            rw [← (hr i').1, (hem (rP i')).1, h, MonoidHom.mul_apply]
          have h6 : μ (em i) z * (μP i' z * NumberField.TateGlobal.normPowChar K (τ (rP i')) z) = μ (em i) z * ν (em i) z := by
            rw [mul_left_comm, ← h3, h4, h5]
          exact mul_left_cancel h6
        exact (AutomorphicForm.integrable_and_setIntegral_inv_ideleNorm_smul_integral_lineIntegral_mul_conj_eq_of_isInducedSection_of_eq_mul_normPowChar K hαm D hDm hDF V hV0 hVT hV
          (μP i') (νP i') (hμPu i') (hνPu i') (hμPic i') (hνPic i') (hμPc i')
          (ψf i') (hψf i') (hψjc i') (hψhol i') (hψdec i') (ν (em i)) (μ (em i)) (hνu (em i)) (hνic (em i)) (-(t + τ i)) (fun g : AdelicGL2 (𝓞 K) K => vol⁻¹ * NE (em i) j tE g) (hΦN) hNc (-τ (rP i')) (hmatch)).1
      · have hsep : ∃ z, z ∈ NumberField.TateGlobal.normOneIdeles K ∧ μP i' z ≠ ν (em i) z := by
          by_contra hall
          push Not at hall
          apply h
          by_contra hne
          obtain ⟨z, hz, hμz⟩ := sepE (em (rP i')) (em i) hne
          apply hμz
          have h1 : μP i' z = ν (em i) z := by
            have := hall z
            tauto
          have h2 : μ (em (rP i')) z = μP (rP i') z := by
            rw [(hem (rP i')).1, MonoidHom.mul_apply, TorusPairGlue.normPowChar_apply_of_mem_normOneIdeles _ hz, mul_one]
          have h3 : μP (rP i') z = νP i' z := by rw [(hr i').1]
          have h4 : μP i' z * νP i' z = ξK ⟨z, Subgroup.mem_top z⟩ := hμPν i' ⟨z, Subgroup.mem_top z⟩
          have h5 : μ (em i) z * ν (em i) z = ξK ⟨z, Subgroup.mem_top z⟩ := hμν (em i) z
          rw [h2, h3]
          rw [h1] at h4
          have h6 : ν (em i) z * νP i' z = ν (em i) z * μ (em i) z := by rw [h4, ← h5, mul_comm]
          exact mul_left_cancel h6
        obtain ⟨z, hz, hne'⟩ := hsep
        exact (AutomorphicForm.integrable_and_setIntegral_inv_ideleNorm_smul_integral_lineIntegral_mul_conj_eq_zero_of_isInducedSection_of_apply_ne K hαm D hDm hDF V hV0 hVT hV
          (μP i') (νP i') (hμPu i') (hνPu i') (hμPic i') (hνPic i') (hμPc i')
          (ψf i') (hψf i') (hψjc i') (hψhol i') (hψdec i') (ν (em i)) (μ (em i)) (hνu (em i)) (hνic (em i)) (-(t + τ i)) (fun g : AdelicGL2 (𝓞 K) K => vol⁻¹ * NE (em i) j tE g) (hΦN) hNc z hz hne').1

    have hpt : (fun p : (AdeleRing (𝓞 K) K)ˣ × adelicMaximalCompact K =>
          ψ (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K)) *
            conj ((fun g : AdelicGL2 (𝓞 K) K => φE (em i) j tE g + vol⁻¹ * NE (em i) j tE g)
              (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K)))) =
        fun p => (((4 * Real.pi)⁻¹ : ℝ) : ℂ) * ∑ i' : ιP,
          ((∫ t' : ℝ, ψf i' ((t' : ℂ) * Complex.I) (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K))) *
              conj ((fun g : AdelicGL2 (𝓞 K) K => φE (em i) j tE g) (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K))) +
           (∫ t' : ℝ, ψf i' ((t' : ℂ) * Complex.I) (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K))) *
              conj ((fun g : AdelicGL2 (𝓞 K) K => vol⁻¹ * NE (em i) j tE g) (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K)))) := by
      funext p
      rw [hψrep 0 (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K))]
      simp only [Complex.ofReal_zero, zero_add, Finset.sum_mul, Finset.mul_sum, map_add]
      refine Finset.sum_congr rfl fun i' _ => ?_
      ring
    have hIψ : Integrable (fun p : (AdeleRing (𝓞 K) K)ˣ × adelicMaximalCompact K =>
          ψ (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K)) *
            conj ((fun g : AdelicGL2 (𝓞 K) K => φE (em i) j tE g + vol⁻¹ * NE (em i) j tE g)
              (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K)))) ((((NumberField.Idele.idelicHaar K).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 K) K)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹))).prod (maximalCompactHaar K)) := by
      rw [hpt]
      exact (integrable_finsetSum _ fun i' _ => (hIφ i').add (hIN i')).const_mul _

    have key : ∀ (F : (AdeleRing (𝓞 K) K)ˣ × adelicMaximalCompact K → ℂ), Integrable F ((((NumberField.Idele.idelicHaar K).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 K) K)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹))).prod (maximalCompactHaar K)) →
        (∫ y in D, (NumberField.TateGlobal.ideleNorm K y)⁻¹ • ∫ k, F (y, k) ∂(maximalCompactHaar K)
          ∂(NumberField.Idele.idelicHaar K)) = ∫ p, F p ∂((((NumberField.Idele.idelicHaar K).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 K) K)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹))).prod (maximalCompactHaar K)) := by
      intro F hF
      rw [MeasureTheory.integral_prod F hF,
        integral_withDensity_eq_integral_toReal_smul
          ((NumberField.TateGlobal.continuous_ideleNorm K).measurable.fun_inv.ennreal_ofReal)
          (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      refine setIntegral_congr_fun hDm fun y _ => ?_
      rw [ENNReal.toReal_ofReal (inv_nonneg.2 (NumberField.TateGlobal.ideleNorm_pos (F := K) y).le)]
    have hsplit :
        (∫ y in D, (NumberField.TateGlobal.ideleNorm K y)⁻¹ •
            ∫ k, ψ (diagOne y * (k : AdelicGL2 (𝓞 K) K)) * conj ((fun g => φE (em i) j tE g + vol⁻¹ * NE (em i) j tE g) (diagOne y * (k : AdelicGL2 (𝓞 K) K))) ∂(maximalCompactHaar K)
          ∂(NumberField.Idele.idelicHaar K)) =
        (((4 * Real.pi)⁻¹ : ℝ) : ℂ) * ∑ i' : ιP,
          ((∫ y in D, (NumberField.TateGlobal.ideleNorm K y)⁻¹ •
              ∫ k, (∫ t' : ℝ, ψf i' ((t' : ℂ) * Complex.I) (diagOne y * (k : AdelicGL2 (𝓞 K) K))) *
                  conj ((fun g => φE (em i) j tE g) (diagOne y * (k : AdelicGL2 (𝓞 K) K))) ∂(maximalCompactHaar K)
            ∂(NumberField.Idele.idelicHaar K)) +
           (∫ y in D, (NumberField.TateGlobal.ideleNorm K y)⁻¹ •
              ∫ k, (∫ t' : ℝ, ψf i' ((t' : ℂ) * Complex.I) (diagOne y * (k : AdelicGL2 (𝓞 K) K))) *
                  conj ((fun g => vol⁻¹ * NE (em i) j tE g) (diagOne y * (k : AdelicGL2 (𝓞 K) K))) ∂(maximalCompactHaar K)
            ∂(NumberField.Idele.idelicHaar K))) := by
      rw [key _ hIψ, hpt, integral_const_mul, integral_finsetSum Finset.univ fun i' _ =>
        (show Integrable (fun p : (AdeleRing (𝓞 K) K)ˣ × adelicMaximalCompact K => _ + _) _ from (hIφ i').add (hIN i'))]
      congr 1
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [integral_add (hIφ i') (hIN i'), key _ (hIφ i'), key _ (hIN i')]

    have hφ : ∀ i' : ιP, (∫ y in D, (NumberField.TateGlobal.ideleNorm K y)⁻¹ •
              ∫ k, (∫ t' : ℝ, ψf i' ((t' : ℂ) * Complex.I) (diagOne y * (k : AdelicGL2 (𝓞 K) K))) *
                  conj ((fun g => φE (em i) j tE g) (diagOne y * (k : AdelicGL2 (𝓞 K) K))) ∂(maximalCompactHaar K)
            ∂(NumberField.Idele.idelicHaar K)) =
        if i' = i then ((V.toReal * (2 * Real.pi) : ℝ) : ℂ) *
          ∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j tE (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) else 0 := by
      intro i'
      by_cases hii : i' = i
      · rw [if_pos hii, hii]
        have H := (AutomorphicForm.integrable_and_setIntegral_inv_ideleNorm_smul_integral_lineIntegral_mul_conj_eq_of_isInducedSection_of_eq_mul_normPowChar K hαm D hDm hDF V hV0 hVT hV
          (μP i) (νP i) (hμPu i) (hνPu i) (hμPic i) (hνPic i) (hμPc i)
          (ψf i) (hψf i) (hψjc i) (hψhol i) (hψdec i) (μ (em i)) (ν (em i)) (hμu (em i)) (hμic (em i)) (t + τ i) (fun g : AdelicGL2 (𝓞 K) K => φE (em i) j tE g) (hφE (em i) j tE) hφc (τ i) ((hem i).1)).2
        rw [add_sub_cancel_right] at H
        exact H
      · rw [if_neg hii]
        obtain ⟨z, hz, hne⟩ := sepP i' i hii
        have hne' : μP i' z ≠ μ (em i) z := by
          rwa [(hem i).1, MonoidHom.mul_apply, TorusPairGlue.normPowChar_apply_of_mem_normOneIdeles _ hz, mul_one] at hne
        exact (AutomorphicForm.integrable_and_setIntegral_inv_ideleNorm_smul_integral_lineIntegral_mul_conj_eq_zero_of_isInducedSection_of_apply_ne K hαm D hDm hDF V hV0 hVT hV
          (μP i') (νP i') (hμPu i') (hνPu i') (hμPic i') (hνPic i') (hμPc i')
          (ψf i') (hψf i') (hψjc i') (hψhol i') (hψdec i') (μ (em i)) (ν (em i)) (hμu (em i)) (hμic (em i)) (t + τ i) (fun g : AdelicGL2 (𝓞 K) K => φE (em i) j tE g) (hφE (em i) j tE) hφc z hz hne').2

    have hN : ∀ i' : ιP, (∫ y in D, (NumberField.TateGlobal.ideleNorm K y)⁻¹ •
              ∫ k, (∫ t' : ℝ, ψf i' ((t' : ℂ) * Complex.I) (diagOne y * (k : AdelicGL2 (𝓞 K) K))) *
                  conj ((fun g => vol⁻¹ * NE (em i) j tE g) (diagOne y * (k : AdelicGL2 (𝓞 K) K))) ∂(maximalCompactHaar K)
            ∂(NumberField.Idele.idelicHaar K)) =
        if i' = rP i then ((V.toReal * (2 * Real.pi) : ℝ) : ℂ) *
          ∫ k, ψf (rP i) (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) * conj (vol⁻¹ * NE (em i) j tE (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)
        else 0 := by
      intro i'
      by_cases hii : i' = rP i
      · rw [if_pos hii, hii]
        have hmatch : μP (rP i) = ν (em i) * NumberField.TateGlobal.normPowChar K (-τ i) := by
          rw [(hr i).1, (hem i).2, TorusPairGlue.normPowChar_inv]
        have H := (AutomorphicForm.integrable_and_setIntegral_inv_ideleNorm_smul_integral_lineIntegral_mul_conj_eq_of_isInducedSection_of_eq_mul_normPowChar K hαm D hDm hDF V hV0 hVT hV
          (μP (rP i)) (νP (rP i)) (hμPu (rP i)) (hνPu (rP i)) (hμPic (rP i)) (hνPic (rP i)) (hμPc (rP i))
          (ψf (rP i)) (hψf (rP i)) (hψjc (rP i)) (hψhol (rP i)) (hψdec (rP i)) (ν (em i)) (μ (em i)) (hνu (em i)) (hνic (em i)) (-(t + τ i)) (fun g : AdelicGL2 (𝓞 K) K => vol⁻¹ * NE (em i) j tE g) (hΦN) hNc (-τ i) (hmatch)).2
        have hc2 : (((-(t + τ i) - -τ i : ℝ) : ℂ) * Complex.I) = -((t : ℂ) * Complex.I) := by
          push_cast
          ring
        rw [hc2] at H
        exact H
      · rw [if_neg hii]
        obtain ⟨z, hz, hne⟩ := sepP i' (rP i) hii
        have hne' : μP i' z ≠ ν (em i) z := by
          rwa [(hr i).1, (hem i).2, MonoidHom.mul_apply, TorusPairGlue.normPowChar_inv,
            TorusPairGlue.normPowChar_apply_of_mem_normOneIdeles _ hz, mul_one] at hne
        exact (AutomorphicForm.integrable_and_setIntegral_inv_ideleNorm_smul_integral_lineIntegral_mul_conj_eq_zero_of_isInducedSection_of_apply_ne K hαm D hDm hDF V hV0 hVT hV
          (μP i') (νP i') (hμPu i') (hνPu i') (hμPic i') (hνPic i') (hμPc i')
          (ψf i') (hψf i') (hψjc i') (hψhol i') (hψdec i') (ν (em i)) (μ (em i)) (hνu (em i)) (hνic (em i)) (-(t + τ i)) (fun g : AdelicGL2 (𝓞 K) K => vol⁻¹ * NE (em i) j tE g) (hΦN) hNc z hz hne').2
    rw [hsplit]
    simp_rw [hφ, hN]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp
    ring

end S_AutomorphicForm_exists_forall_setIntegral_inv_ideleNorm_smul_integral_maximalCompact_mul_conj_constantTerm_eq_of_matched_paleyWiener
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_setIntegral_inv_ideleNorm_smul_integral_maximalCompact_mul_conj_constantTerm_eq_of_matched_paleyWiener (solution)
