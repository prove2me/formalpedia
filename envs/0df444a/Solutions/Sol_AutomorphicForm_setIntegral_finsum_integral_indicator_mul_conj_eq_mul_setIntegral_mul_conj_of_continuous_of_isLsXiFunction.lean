-- Prove2me | solution 1 for AutomorphicForm.setIntegral_finsum_integral_indicator_mul_conj_eq_mul_setIntegral_mul_conj_of_continuous_of_isLsXiFunction
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/e6281647-0d9e-5c55-8871-971d2b2b3658

import Theorems.Thm_AutomorphicForm_setIntegral_finsum_integral_indicator_mul_conj_eq_mul_setIntegral_mul_conj_of_isAutomorphicFnAt
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setIntegral_finsum_integral_indicator_mul_conj_eq_mul_setIntegral_mul_conj_of_continuous_of_isLsXiFunction
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open AutomorphicForm

theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (Ψ : AdelicGL2 (𝓞 K) K → ℂ) (_hΨm : Measurable Ψ)
    (_hΨc : ∃ C : Set (AdelicGL2 (𝓞 K) K), IsCompact C ∧ ∀ y ∉ C, Ψ y = 0)
    (_hΨb : ∃ B : ℝ, ∀ y, ‖Ψ y‖ ≤ B)
    (u : AdelicGL2 (𝓞 K) K → ℂ) (_huc : Continuous u)
    (_hu : IsLsXiFunction (𝓞 K) K ⊤ ξK u) :
    ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) g * conj (u g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) *
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, Ψ g * conj (u g)
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  obtain ⟨-, -, -, hslab, hFD⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ
  have hfin : adelicGLHaar (Fin 2) (𝓞 K) K (AutomorphicForm.canonicalTruncationDomain K α β) < ⊤ := by
    have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain K α β hα hαβ
      (AutomorphicForm.canonicalTruncationDomain K α β) hFD
    rwa [Set.inter_eq_left.mpr hslab] at h
  haveI : IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) :=
    isFiniteMeasure_restrict.2 hfin.ne
  have hcomm : ∀ (w : (AdeleRing (𝓞 K) K)ˣ) (x y : AdelicGL2 (𝓞 K) K),
      centralScalar (𝓞 K) K w * (x * y) = x * (centralScalar (𝓞 K) K w * y) := by
    intro w x y
    rw [← mul_assoc, ← mul_centralScalar_comm w x, mul_assoc]

  obtain ⟨C, hC, hΨC⟩ := _hΨc
  obtain ⟨O, hO, hCO, hOc⟩ := exists_isOpen_superset_and_isCompact_closure hC

  set E : Set (AdelicGL2 (𝓞 K) K) := ⋃ z : (AdeleRing (𝓞 K) K)ˣ, ⋃ γ : GL (Fin 2) K,
    (fun g => centralScalar (𝓞 K) K z * (globalPoints (𝓞 K) K γ * g)) ⁻¹' O with hE
  have hmemE : ∀ g : AdelicGL2 (𝓞 K) K, g ∈ E ↔ ∃ (z : (AdeleRing (𝓞 K) K)ˣ) (γ : GL (Fin 2) K),
      centralScalar (𝓞 K) K z * (globalPoints (𝓞 K) K γ * g) ∈ O := fun g => by
    simp only [hE, Set.mem_iUnion, Set.mem_preimage]
  have hEo : IsOpen E := isOpen_iUnion fun z => isOpen_iUnion fun γ =>
    hO.preimage (continuous_const.mul (continuous_const.mul continuous_id))
  have hEΓ : ∀ (γ₀ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), globalPoints (𝓞 K) K γ₀ * g ∈ E ↔ g ∈ E := by
    intro γ₀ g
    rw [hmemE, hmemE]
    constructor
    · rintro ⟨z, γ, h⟩
      exact ⟨z, γ * γ₀, by rwa [map_mul, mul_assoc]⟩
    · rintro ⟨z, γ, h⟩
      exact ⟨z, γ * γ₀⁻¹, by rwa [map_mul, map_inv, mul_assoc, inv_mul_cancel_left]⟩
  have hEZ : ∀ (z₀ : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K), centralScalar (𝓞 K) K z₀ * g ∈ E ↔ g ∈ E := by
    intro z₀ g
    rw [hmemE, hmemE]
    constructor
    · rintro ⟨z, γ, h⟩
      refine ⟨z * z₀, γ, ?_⟩
      rw [map_mul, mul_assoc, hcomm z₀]
      exact h
    · rintro ⟨z, γ, h⟩
      refine ⟨z * z₀⁻¹, γ, ?_⟩
      rw [map_mul, mul_assoc, hcomm z₀⁻¹, map_inv, inv_mul_cancel_left]
      exact h

  have hL' : IsLsXiFunction (𝓞 K) K ⊤ ξK (E.indicator u) := by
    refine ⟨fun γ g => ?_, fun z g => ?_⟩
    · by_cases hg : g ∈ E
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem ((hEΓ γ g).2 hg), _hu.left_invariant]
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg ((hEΓ γ g).1 h))]
    · by_cases hg : g ∈ E
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem ((hEZ _ g).2 hg), _hu.central_transform]
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg ((hEZ _ g).1 h)), mul_zero]
  obtain ⟨M, hM⟩ := hOc.exists_bound_of_continuousOn _huc.continuousOn
  have hbd : ∀ g : AdelicGL2 (𝓞 K) K, ‖E.indicator u g‖ ≤ max M 0 := by
    intro g
    by_cases hg : g ∈ E
    · rw [Set.indicator_of_mem hg]
      obtain ⟨z, γ, h⟩ := (hmemE g).1 hg
      have h1 : u (centralScalar (𝓞 K) K z * (globalPoints (𝓞 K) K γ * g)) =
          ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * u g := by
        rw [_hu.central_transform ⟨z, Subgroup.mem_top z⟩, _hu.left_invariant]
      have h2 : ‖u g‖ = ‖u (centralScalar (𝓞 K) K z * (globalPoints (𝓞 K) K γ * g))‖ := by
        rw [h1, norm_mul, hξu z, one_mul]
      rw [h2]
      exact (hM _ (subset_closure h)).trans (le_max_left _ _)
    · rw [Set.indicator_of_notMem hg, norm_zero]; exact le_max_right _ _
  have hMem : MemLp (E.indicator u) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) :=
    MemLp.of_bound (_huc.aestronglyMeasurable.indicator hEo.measurableSet) (max M 0)
      (Filter.Eventually.of_forall hbd)
  have hu'A : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
      (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
      (adelicBox K)) ξK (E.indicator u) :=
    (lsXiMemberAt_iff _ _ _ _ _ _ _).2 ⟨hL', hMem⟩

  have hT5 := AutomorphicForm.setIntegral_finsum_integral_indicator_mul_conj_eq_mul_setIntegral_mul_conj_of_isAutomorphicFnAt
    K α β hα hαβ νZK ΩK hΩK ξK hξc hξt hξu Ψ _hΨm ⟨C, hC, hΨC⟩ _hΨb (E.indicator u) hu'A

  have hΨE : ∀ g : AdelicGL2 (𝓞 K) K, g ∉ E → Ψ g = 0 := by
    intro g hg
    apply hΨC
    intro hgC
    exact hg ((hmemE g).2 ⟨1, 1, by simpa using hCO hgC⟩)
  have hθE : ∀ g : AdelicGL2 (𝓞 K) K, g ∉ E →
      (∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
        ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
          (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
            (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) = 0 := by
    intro g hg
    have hzero : ∀ (w : (AdeleRing (𝓞 K) K)ˣ) (γ : GL (Fin 2) K),
        (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
          (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K γ * g)) = 0 := by
      intro w γ
      have hnot : centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K γ * g) ∉ O := fun h => hg ((hmemE g).2 ⟨w, γ, h⟩)
      have hΨ0 : Ψ (centralScalar (𝓞 K) K w * (globalPoints (𝓞 K) K γ * g)) = 0 := hΨC _ fun h => hnot (hCO h)
      exact Set.indicator_apply_eq_zero.2 fun _ => hΨ0
    simp only [hzero, mul_zero, integral_zero, finsum_zero]
  have hL : ∀ g : AdelicGL2 (𝓞 K) K,
      (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) g * conj (u g) =
      (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) g *
        conj (E.indicator u g) := by
    intro g
    by_cases hg : g ∈ E
    · rw [Set.indicator_of_mem hg]
    · simp only [hθE g hg, zero_mul]
  have hR : ∀ g : AdelicGL2 (𝓞 K) K, Ψ g * conj (u g) = Ψ g * conj (E.indicator u g) := by
    intro g
    by_cases hg : g ∈ E
    · rw [Set.indicator_of_mem hg]
    · simp only [hΨE g hg, zero_mul]
  rw [integral_congr_ae (Filter.Eventually.of_forall hL), integral_congr_ae (Filter.Eventually.of_forall hR)]
  exact hT5

end S_AutomorphicForm_setIntegral_finsum_integral_indicator_mul_conj_eq_mul_setIntegral_mul_conj_of_continuous_of_isLsXiFunction
end P2MW
export P2MW.S_AutomorphicForm_setIntegral_finsum_integral_indicator_mul_conj_eq_mul_setIntegral_mul_conj_of_continuous_of_isLsXiFunction (solution)
