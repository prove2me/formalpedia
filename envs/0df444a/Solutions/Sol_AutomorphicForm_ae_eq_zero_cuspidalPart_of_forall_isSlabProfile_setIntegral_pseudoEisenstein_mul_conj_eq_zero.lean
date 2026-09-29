-- Prove2me | solution 1 for AutomorphicForm.ae_eq_zero_cuspidalPart_of_forall_isSlabProfile_setIntegral_pseudoEisenstein_mul_conj_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/e3b4f126-6622-5cb3-977b-ed83c0cb6ff7

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
import Theorems.Thm_AutomorphicForm_setIntegral_mul_conj_eq_zero_of_ae_constantTerm_eq_zero_of_mem_residualSpan_slab
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_ae_eq_zero_cuspidalPart_of_forall_isSlabProfile_setIntegral_pseudoEisenstein_mul_conj_eq_zero
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace CuspZero19

open InnerProductSpace

section L2

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem inner_toLp_eq {f g : X → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (⟪hf.toLp f, hg.toLp g⟫_ℂ : ℂ) = ∫ x, g x * conj (f x) ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  rw [hfx, hgx, RCLike.inner_apply, mul_comm]

theorem integrable_mul_conj {f g : X → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => g x * conj (f x)) μ := by
  have h := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (hf.toLp f) (hg.toLp g)
  refine h.congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  rw [hfx, hgx, RCLike.inner_apply, mul_comm]

theorem norm_integral_mul_conj_le {f g : X → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖∫ x, g x * conj (f x) ∂μ‖ ≤ (eLpNorm g 2 μ).toReal * (eLpNorm f 2 μ).toReal := by
  rw [← inner_toLp_eq hf hg, mul_comm]
  have := norm_inner_le_norm (𝕜 := ℂ) (hf.toLp f) (hg.toLp g)
  rwa [Lp.norm_toLp, Lp.norm_toLp] at this

end L2

theorem eq_zero_of_forall_le_mul {D L : ℝ} (hD : 0 ≤ D) (hL : 0 ≤ L) (h : ∀ ε > 0, D ≤ L * ε) : D = 0 := by
  by_contra hne
  have hDpos : 0 < D := lt_of_le_of_ne hD (Ne.symm hne)
  have := h (D / (2 * (L + 1))) (by positivity)
  have hL1 : 0 < L + 1 := by linarith
  have hle : D ≤ L * (D / (2 * (L + 1))) := this
  have hlt : L * (D / (2 * (L + 1))) < D := by
    have hq : L / (2 * (L + 1)) < 1 := by
      rw [div_lt_one (by positivity)]; linarith
    calc L * (D / (2 * (L + 1))) = D * (L / (2 * (L + 1))) := by ring
      _ < D * 1 := mul_lt_mul_of_pos_left hq hDpos
      _ = D := mul_one D
  linarith

theorem measure_canonicalTruncationDomain_lt_top (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) :
    adelicGLHaar (Fin 2) (𝓞 K) K (AutomorphicForm.canonicalTruncationDomain K α β) < ⊤ := by
  by_cases h : ∃ d, AutomorphicForm.IsTruncationDatum K α β d
  · have hspec := AutomorphicForm.canonicalTruncationData_spec K h
    obtain ⟨-, -, -, hsub, hFD⟩ := hspec
    have := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
      K α β hα hαβ (AutomorphicForm.canonicalTruncationDomain K α β) hFD
    exact lt_of_le_of_lt (measure_mono (Set.subset_inter Set.Subset.rfl hsub)) this
  · have : AutomorphicForm.canonicalTruncationDomain K α β = ∅ := by
      show (AutomorphicForm.canonicalTruncationData K α β).2.2 = ∅
      unfold AutomorphicForm.canonicalTruncationData
      rw [dif_neg h]
    rw [this, measure_empty]
    exact ENNReal.zero_lt_top

end CuspZero19

section MainProof

set_option hygiene false in
local notation "PINS" => productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
    (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)

open AutomorphicForm CuspZero19 in

theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (θ : AdelicGL2 (𝓞 K) K → ℂ)
    (_hθ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK θ) :
    letI := adeleBorel (𝓞 K) K
    ∀ (_hθo : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 h g = 0) →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, θ g * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (uc ur ue : AdelicGL2 (𝓞 K) K → ℂ)
      (_huc : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK uc) (_huc0 : (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 uc g = 0))
      (_hur : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ur)
      (_hurc : ∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r ∧ eLpNorm (ur - r) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε)
      (_hue : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ue)
      (_hueo : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        ((∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 h g = 0) ∨ h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK) →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, ue g * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (_hsum : θ =ᵐ[((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))] uc + ur + ue),
    uc =ᵐ[((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))] 0 ∧
    (∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, (θ g - ur g) * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0) := by
  intro hθo uc ur ue huc huc0 hur hurc hue hueo hsum
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  set Φ := AutomorphicForm.canonicalTruncationDomain K α β with hΦ

  by_cases hdat : ∃ d, IsTruncationDatum K α β d
  swap
  · have hempty : Φ = ∅ := by
      show (AutomorphicForm.canonicalTruncationData K α β).2.2 = ∅
      unfold AutomorphicForm.canonicalTruncationData
      rw [dif_neg hdat]
    have h0 : μ.restrict Φ = 0 := by rw [hempty, Measure.restrict_empty]
    refine ⟨?_, fun h _ _ => ?_⟩
    · rw [h0, Filter.EventuallyEq, ae_zero]; exact Filter.eventually_bot
    · show ∫ g, (θ g - ur g) * conj (h g) ∂(μ.restrict Φ) = 0
      rw [h0, integral_zero_measure]

  obtain ⟨-, -, -, hsub, hFD⟩ := AutomorphicForm.canonicalTruncationData_spec K hdat
  haveI : IsFiniteMeasure (μ.restrict Φ) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_canonicalTruncationDomain_lt_top K α β hα hαβ⟩
  have hL2 : ∀ {u : AdelicGL2 (𝓞 K) K → ℂ}, IsAutomorphicFnAt K PINS ξK u → MemLp u 2 (μ.restrict Φ) :=
    fun {u} hu => ((lsXiMemberAt_iff (𝓞 K) K μ ⊤ ξK Φ u).1 hu).2

  have hcr : ∀ r : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K PINS ξK r →
      r ∈ AutomorphicForm.residualSpan (𝓞 K) K (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) ξK →
      ∫ g in Φ, uc g * conj (r g) ∂μ = 0 := fun r hr hres =>
    AutomorphicForm.setIntegral_mul_conj_eq_zero_of_ae_constantTerm_eq_zero_of_mem_residualSpan_slab
      K α β hα hαβ Φ hsub hFD ξK uc huc huc0 r hr hres

  have hip_ur : ∫ g in Φ, ur g * conj (uc g) ∂μ = 0 := by
    rw [← norm_eq_zero]
    refine eq_zero_of_forall_le_mul (norm_nonneg _) ENNReal.toReal_nonneg (L := (eLpNorm uc 2 (μ.restrict Φ)).toReal)
      fun ε hε => ?_
    obtain ⟨r, hrR, hra, hre⟩ := hurc ε hε
    have hεr : (eLpNorm (ur - r) 2 (μ.restrict Φ)).toReal < ε := ENNReal.toReal_lt_of_lt_ofReal hre
    have I12 := integrable_mul_conj (hL2 huc) ((hL2 hur).sub (hL2 hra))
    have I2 := integrable_mul_conj (hL2 huc) (hL2 hra)
    have hsplit : ∫ g in Φ, ur g * conj (uc g) ∂μ =
        ∫ g in Φ, (ur - r) g * conj (uc g) ∂μ + ∫ g in Φ, r g * conj (uc g) ∂μ := by
      calc ∫ g in Φ, ur g * conj (uc g) ∂μ
          = ∫ g in Φ, ((ur - r) g * conj (uc g) + r g * conj (uc g)) ∂μ := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
            simp only [Pi.sub_apply]; ring
        _ = _ := integral_add I12 I2
    have hr0 : ∫ g in Φ, r g * conj (uc g) ∂μ = 0 := by
      have h := hcr r hra hrR
      have : ∫ g in Φ, r g * conj (uc g) ∂μ = conj (∫ g in Φ, uc g * conj (r g) ∂μ) := by
        rw [← integral_conj]
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        simp [mul_comm]
      rw [this, h, map_zero]
    rw [hsplit, hr0, add_zero]
    refine (norm_integral_mul_conj_le (hL2 huc) ((hL2 hur).sub (hL2 hra))).trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left hεr.le ENNReal.toReal_nonneg

  have hip_ue : ∫ g in Φ, ue g * conj (uc g) ∂μ = 0 := hueo uc huc (Or.inl huc0)
  have hip_θ : ∫ g in Φ, θ g * conj (uc g) ∂μ = 0 := hθo uc huc huc0
  have Ic := integrable_mul_conj (hL2 huc) (hL2 huc)
  have Ir := integrable_mul_conj (hL2 huc) (hL2 hur)
  have Ie := integrable_mul_conj (hL2 huc) (hL2 hue)
  have hsq : ∫ g in Φ, uc g * conj (uc g) ∂μ = 0 := by
    have h3 : ∫ g in Φ, θ g * conj (uc g) ∂μ =
        ∫ g in Φ, uc g * conj (uc g) ∂μ + ∫ g in Φ, ur g * conj (uc g) ∂μ + ∫ g in Φ, ue g * conj (uc g) ∂μ := by
      calc ∫ g in Φ, θ g * conj (uc g) ∂μ
          = ∫ g in Φ, ((uc g * conj (uc g) + ur g * conj (uc g)) + ue g * conj (uc g)) ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards [hsum] with g hg
            rw [hg]
            simp only [Pi.add_apply, add_mul]
        _ = ∫ g in Φ, (uc g * conj (uc g) + ur g * conj (uc g)) ∂μ + ∫ g in Φ, ue g * conj (uc g) ∂μ :=
            integral_add (Ic.add Ir) Ie
        _ = _ := by rw [integral_add Ic Ir]
    rw [hip_θ, hip_ur, hip_ue, add_zero, add_zero] at h3
    exact h3.symm
  have hsqR : ∫ g in Φ, ‖uc g‖ ^ 2 ∂μ = 0 := by
    have : ∫ g in Φ, uc g * conj (uc g) ∂μ = ((∫ g in Φ, ‖uc g‖ ^ 2 ∂μ : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      dsimp only
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
    rw [this] at hsq
    exact_mod_cast hsq
  have hint2 : Integrable (fun g => ‖uc g‖ ^ 2) (μ.restrict Φ) :=
    (memLp_two_iff_integrable_sq_norm (hL2 huc).1).1 (hL2 huc)
  have hae := (integral_eq_zero_iff_of_nonneg (fun g => sq_nonneg _) hint2).1 hsqR
  refine ⟨?_, ?_⟩
  · filter_upwards [hae] with g hg
    have : ‖uc g‖ = 0 := by
      have h' : ‖uc g‖ ^ 2 = 0 := hg
      exact pow_eq_zero_iff two_ne_zero |>.1 h'
    simpa using this

  · intro h hh hres
    have Ih := fun {u} (hu : IsAutomorphicFnAt K PINS ξK u) => integrable_mul_conj (hL2 hh) (hL2 hu)
    have h4 : ∫ g in Φ, (θ g - ur g) * conj (h g) ∂μ =
        ∫ g in Φ, uc g * conj (h g) ∂μ + ∫ g in Φ, ue g * conj (h g) ∂μ := by
      calc ∫ g in Φ, (θ g - ur g) * conj (h g) ∂μ
          = ∫ g in Φ, (uc g * conj (h g) + ue g * conj (h g)) ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards [hsum] with g hg
            rw [hg]
            simp only [Pi.add_apply]; ring
        _ = _ := integral_add (Ih huc) (Ih hue)
    rw [h4, hcr h hh hres, hueo h hh (Or.inr hres), add_zero]

end MainProof

end S_AutomorphicForm_ae_eq_zero_cuspidalPart_of_forall_isSlabProfile_setIntegral_pseudoEisenstein_mul_conj_eq_zero
end P2MW
export P2MW.S_AutomorphicForm_ae_eq_zero_cuspidalPart_of_forall_isSlabProfile_setIntegral_pseudoEisenstein_mul_conj_eq_zero (solution)
