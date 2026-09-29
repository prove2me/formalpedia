-- Prove2me | solution 1 for AutomorphicForm.setIntegral_continuousPart_mul_conj_convOp_continuousPart_eq_sub_of_pseudoEisenstein_threeWay
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/74d14fe1-a795-5559-9d68-38e8b2de9cae

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
import Theorems.Thm_AutomorphicForm_convOp_eq_add_add_of_ae_eq_restrict_canonicalTruncationDomain_of_isAutomorphicFnAt_of_continuous
import Theorems.Thm_AutomorphicForm_isAutomorphicFnAt_convOp_of_isAutomorphicFnAt_canonicalTruncationDomain
import Theorems.Thm_AutomorphicForm_isAutomorphicFnAt_pseudoEisenstein_slab
import Theorems.Thm_AutomorphicForm_ae_constantTerm_eq_zero_iff_forall_setIntegral_pseudoEisenstein_mul_conj_eq_zero_slab
import Theorems.Thm_AutomorphicForm_ae_eq_zero_cuspidalPart_of_forall_isSlabProfile_setIntegral_pseudoEisenstein_mul_conj_eq_zero
import Theorems.Thm_AutomorphicForm_convOp_residualProjection_of_residualProjection
import Theorems.Thm_AutomorphicForm_setIntegral_mul_conj_eq_zero_of_forall_residualSpan_of_closure
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setIntegral_continuousPart_mul_conj_convOp_continuousPart_eq_sub_of_pseudoEisenstein_threeWay
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.ArchDirComplex.iH.sizeOf_spec"
p2m_attr_erase "simp" "AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace P1Alg19

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

end P1Alg19

namespace P1Alg19

open AutomorphicForm

theorem aut_sub' (K : Type) [Field K] [NumberField K] (α β : ℝ)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) {u v : AdelicGL2 (𝓞 K) K → ℂ}
    (hu : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
      (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK u)
    (hv : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
      (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK v) :
    IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
      (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK (u - v) := by
  have hu' := (AutomorphicForm.lsXiMemberAt_iff (𝓞 K) K (adelicGLHaar (Fin 2) (𝓞 K) K) ⊤ ξK
    (AutomorphicForm.canonicalTruncationDomain K α β) u).1 hu
  have hv' := (AutomorphicForm.lsXiMemberAt_iff (𝓞 K) K (adelicGLHaar (Fin 2) (𝓞 K) K) ⊤ ξK
    (AutomorphicForm.canonicalTruncationDomain K α β) v).1 hv
  refine (AutomorphicForm.lsXiMemberAt_iff (𝓞 K) K (adelicGLHaar (Fin 2) (𝓞 K) K) ⊤ ξK
    (AutomorphicForm.canonicalTruncationDomain K α β) (u - v)).2 ⟨⟨fun γ g => ?_, fun z g => ?_⟩, hu'.2.sub hv'.2⟩
  · simp only [Pi.sub_apply, hu'.1.left_invariant, hv'.1.left_invariant]
  · simp only [Pi.sub_apply, hu'.1.central_transform, hv'.1.central_transform, mul_sub]

end P1Alg19

section MainProof

set_option hygiene false in
local notation "PINS" => productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
    (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)

open AutomorphicForm P1Alg19 in

theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
    (φ ψ : AdelicGL2 (𝓞 K) K → ℂ)
    (_hφ : AutomorphicForm.IsSlabProfile K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK φ)
    (_hψ : AutomorphicForm.IsSlabProfile K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK ψ) :
    letI := adeleBorel (𝓞 K) K
    ∀
      (uc₁ ur₁ ue₁ : AdelicGL2 (𝓞 K) K → ℂ)
      (_huc₁ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK uc₁) (_huc0₁ : (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 uc₁ g = 0))
      (_hur₁ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ur₁)
      (_hurc₁ : ∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r ∧ eLpNorm (ur₁ - r) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε)
      (_hue₁ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ue₁)
      (_hueo₁ : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        ((∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 h g = 0) ∨ h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK) →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, ue₁ g * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (_hsum₁ : AutomorphicForm.pseudoEisenstein K φ =ᵐ[((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))] uc₁ + ur₁ + ue₁)
      (uc₂ ur₂ ue₂ : AdelicGL2 (𝓞 K) K → ℂ)
      (_huc₂ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK uc₂) (_huc0₂ : (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 uc₂ g = 0))
      (_hur₂ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ur₂)
      (_hurc₂ : ∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r ∧ eLpNorm (ur₂ - r) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε)
      (_hue₂ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ue₂)
      (_hueo₂ : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        ((∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 h g = 0) ∨ h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK) →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, ue₂ g * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (_hsum₂ : AutomorphicForm.pseudoEisenstein K ψ =ᵐ[((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))] uc₂ + ur₂ + ue₂),
    ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        ue₁ g * conj (convOp K f ue₂ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      (∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          AutomorphicForm.pseudoEisenstein K φ g * conj (convOp K f (AutomorphicForm.pseudoEisenstein K ψ) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) -
      ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          ur₁ g * conj (convOp K f ur₂ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  intro uc₁ ur₁ ue₁ huc₁ huc0₁ hur₁ hurc₁ hue₁ hueo₁ hsum₁ uc₂ ur₂ ue₂ huc₂ huc0₂ hur₂ hurc₂ hue₂ hueo₂ hsum₂
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  set Φ := AutomorphicForm.canonicalTruncationDomain K α β with hΦ
  set θ₁ := AutomorphicForm.pseudoEisenstein K φ with hθ₁
  set θ₂ := AutomorphicForm.pseudoEisenstein K ψ with hθ₂

  by_cases hdat : ∃ d, IsTruncationDatum K α β d
  swap
  · have hempty : Φ = ∅ := by
      show (AutomorphicForm.canonicalTruncationData K α β).2.2 = ∅
      unfold AutomorphicForm.canonicalTruncationData
      rw [dif_neg hdat]
    have h0 : μ.restrict Φ = 0 := by rw [hempty, Measure.restrict_empty]
    show ∫ g, _ ∂(μ.restrict Φ) = (∫ g, _ ∂(μ.restrict Φ)) - ∫ g, _ ∂(μ.restrict Φ)
    rw [h0, integral_zero_measure, integral_zero_measure, integral_zero_measure, sub_zero]

  obtain ⟨-, -, -, hsub, hFD⟩ := AutomorphicForm.canonicalTruncationData_spec K hdat
  have hL2 : ∀ {u : AdelicGL2 (𝓞 K) K → ℂ}, IsAutomorphicFnAt K PINS ξK u → MemLp u 2 (μ.restrict Φ) :=
    fun {u} hu => ((lsXiMemberAt_iff (𝓞 K) K μ ⊤ ξK Φ u).1 hu).2

  have hξC : Continuous ξK := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · exact hξc.comp continuous_subtype_val
    · have : (fun z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) => ((ξK z)⁻¹ : ℂˣ).val) =
          fun z => ((ξK ⟨z.1, Subgroup.mem_top z.1⟩ : ℂˣ) : ℂ)⁻¹ := by
        funext z; rw [Units.val_inv_eq_inv_val]
      rw [this]
      exact (hξc.comp continuous_subtype_val).inv₀ fun z => Units.ne_zero _

  have hθ₁ : IsAutomorphicFnAt K PINS ξK θ₁ :=
    AutomorphicForm.isAutomorphicFnAt_pseudoEisenstein_slab K α β hα hαβ Φ hsub hFD ξK φ _hφ
  have hθ₂ : IsAutomorphicFnAt K PINS ξK θ₂ :=
    AutomorphicForm.isAutomorphicFnAt_pseudoEisenstein_slab K α β hα hαβ Φ hsub hFD ξK ψ _hψ

  obtain ⟨huc₁0, hperp₁⟩ :=
    AutomorphicForm.ae_eq_zero_cuspidalPart_of_forall_isSlabProfile_setIntegral_pseudoEisenstein_mul_conj_eq_zero
      K α β hα hαβ ξK hξc hξt hξu θ₁ hθ₁
      (fun h hh hcusp => (AutomorphicForm.ae_constantTerm_eq_zero_iff_forall_setIntegral_pseudoEisenstein_mul_conj_eq_zero_slab
        K α β hα hαβ Φ hsub hFD ξK hξC h hh).1 hcusp φ _hφ)
      uc₁ ur₁ ue₁ huc₁ huc0₁ hur₁ hurc₁ hue₁ hueo₁ hsum₁
  obtain ⟨huc₂0, hperp₂⟩ :=
    AutomorphicForm.ae_eq_zero_cuspidalPart_of_forall_isSlabProfile_setIntegral_pseudoEisenstein_mul_conj_eq_zero
      K α β hα hαβ ξK hξc hξt hξu θ₂ hθ₂
      (fun h hh hcusp => (AutomorphicForm.ae_constantTerm_eq_zero_iff_forall_setIntegral_pseudoEisenstein_mul_conj_eq_zero_slab
        K α β hα hαβ Φ hsub hFD ξK hξC h hh).1 hcusp ψ _hψ)
      uc₂ ur₂ ue₂ huc₂ huc0₂ hur₂ hurc₂ hue₂ hueo₂ hsum₂

  obtain ⟨hTur₂, hTur₂c, hTperp⟩ := AutomorphicForm.convOp_residualProjection_of_residualProjection
    K α β hα hαβ ξK hξc hξt hξu f _hf _hfc θ₂ ur₂ hθ₂ hur₂ hurc₂ hperp₂
  have hTue₂ : IsAutomorphicFnAt K PINS ξK (convOp K f ue₂) :=
    AutomorphicForm.isAutomorphicFnAt_convOp_of_isAutomorphicFnAt_canonicalTruncationDomain K α β hα hαβ ξK hξc hξu
      ue₂ hue₂ f _hf _hfc
  have hTθ₂ : IsAutomorphicFnAt K PINS ξK (convOp K f θ₂) :=
    AutomorphicForm.isAutomorphicFnAt_convOp_of_isAutomorphicFnAt_canonicalTruncationDomain K α β hα hαβ ξK hξc hξu
      θ₂ hθ₂ f _hf _hfc
  have h0aut : IsAutomorphicFnAt K PINS ξK (0 : AdelicGL2 (𝓞 K) K → ℂ) := isAutomorphicFnAt_zero K PINS ξK

  have hTuc₂ : ∀ x, convOp K f uc₂ x = 0 := by
    intro x
    have hae : uc₂ =ᵐ[μ.restrict Φ] (0 : AdelicGL2 (𝓞 K) K → ℂ) + 0 + 0 := by
      simpa only [add_zero] using huc₂0
    have := AutomorphicForm.convOp_eq_add_add_of_ae_eq_restrict_canonicalTruncationDomain_of_isAutomorphicFnAt_of_continuous
      K α β hα hαβ ξK hξc uc₂ 0 0 0 huc₂ h0aut h0aut h0aut hae f _hf _hfc x
    rw [this, convOp_zero]; simp
  have hTsplit : ∀ x, convOp K f θ₂ x = convOp K f ur₂ x + convOp K f ue₂ x := by
    intro x
    have := AutomorphicForm.convOp_eq_add_add_of_ae_eq_restrict_canonicalTruncationDomain_of_isAutomorphicFnAt_of_continuous
      K α β hα hαβ ξK hξc θ₂ uc₂ ur₂ ue₂ hθ₂ huc₂ hur₂ hue₂ hsum₂ f _hf _hfc x
    rw [this, hTuc₂, zero_add]

  have hO1 : ∫ g in Φ, ue₁ g * conj (convOp K f ur₂ g) ∂μ = 0 :=
    (AutomorphicForm.setIntegral_mul_conj_eq_zero_of_forall_residualSpan_of_closure K α β hα hαβ ξK ue₁ (convOp K f ur₂)
      hue₁ (fun h hh hres => hueo₁ h hh (Or.inr hres)) hTur₂ hTur₂c).1
  have hO2 : ∫ g in Φ, ur₁ g * conj (convOp K f ue₂ g) ∂μ = 0 := by
    have hx : IsAutomorphicFnAt K PINS ξK (convOp K f θ₂ - convOp K f ur₂) := aut_sub' K α β ξK hTθ₂ hTur₂
    have h := (AutomorphicForm.setIntegral_mul_conj_eq_zero_of_forall_residualSpan_of_closure K α β hα hαβ ξK
      (convOp K f θ₂ - convOp K f ur₂) ur₁ hx (fun h hh hres => hTperp h hh hres) hur₁ hurc₁).2
    refine (integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)).trans h
    simp only [Pi.sub_apply, hTsplit g, add_sub_cancel_left]
  have hO3 : ∫ g in Φ, (θ₁ - ur₁) g * conj (convOp K f ur₂ g) ∂μ = 0 :=
    (AutomorphicForm.setIntegral_mul_conj_eq_zero_of_forall_residualSpan_of_closure K α β hα hαβ ξK (θ₁ - ur₁) (convOp K f ur₂)
      (aut_sub' K α β ξK hθ₁ hur₁) (fun h hh hres => hperp₁ h hh hres) hTur₂ hTur₂c).1

  have Ia := integrable_mul_conj (hL2 hTur₂) (hL2 hθ₁)
  have Ib := integrable_mul_conj (hL2 hTue₂) (hL2 hθ₁)
  have Ic := integrable_mul_conj (hL2 hTur₂) (hL2 hur₁)
  have Id := integrable_mul_conj (hL2 hTur₂) (aut_sub' K α β ξK hθ₁ hur₁ |> hL2)
  have Ie := integrable_mul_conj (hL2 hTue₂) (hL2 hur₁)
  have If := integrable_mul_conj (hL2 hTue₂) (hL2 hue₁)

  have hstep1 : ∫ g in Φ, θ₁ g * conj (convOp K f θ₂ g) ∂μ =
      ∫ g in Φ, θ₁ g * conj (convOp K f ur₂ g) ∂μ + ∫ g in Φ, θ₁ g * conj (convOp K f ue₂ g) ∂μ := by
    calc ∫ g in Φ, θ₁ g * conj (convOp K f θ₂ g) ∂μ
        = ∫ g in Φ, (θ₁ g * conj (convOp K f ur₂ g) + θ₁ g * conj (convOp K f ue₂ g)) ∂μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
          dsimp only
          rw [hTsplit g, map_add, mul_add]
      _ = _ := integral_add Ia Ib

  have hstep2 : ∫ g in Φ, θ₁ g * conj (convOp K f ur₂ g) ∂μ = ∫ g in Φ, ur₁ g * conj (convOp K f ur₂ g) ∂μ := by
    calc ∫ g in Φ, θ₁ g * conj (convOp K f ur₂ g) ∂μ
        = ∫ g in Φ, (ur₁ g * conj (convOp K f ur₂ g) + (θ₁ - ur₁) g * conj (convOp K f ur₂ g)) ∂μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
          simp only [Pi.sub_apply]; ring
      _ = ∫ g in Φ, ur₁ g * conj (convOp K f ur₂ g) ∂μ + ∫ g in Φ, (θ₁ - ur₁) g * conj (convOp K f ur₂ g) ∂μ :=
          integral_add Ic Id
      _ = _ := by rw [hO3, add_zero]

  have hstep3 : ∫ g in Φ, θ₁ g * conj (convOp K f ue₂ g) ∂μ = ∫ g in Φ, ue₁ g * conj (convOp K f ue₂ g) ∂μ := by
    have hae : ∀ᵐ g ∂(μ.restrict Φ), θ₁ g = ur₁ g + ue₁ g := by
      filter_upwards [hsum₁, huc₁0] with g h1 h2
      rw [h1]; simp only [Pi.add_apply, h2, Pi.zero_apply, zero_add]
    calc ∫ g in Φ, θ₁ g * conj (convOp K f ue₂ g) ∂μ
        = ∫ g in Φ, (ur₁ g * conj (convOp K f ue₂ g) + ue₁ g * conj (convOp K f ue₂ g)) ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [hae] with g hg
          rw [hg, add_mul]
      _ = ∫ g in Φ, ur₁ g * conj (convOp K f ue₂ g) ∂μ + ∫ g in Φ, ue₁ g * conj (convOp K f ue₂ g) ∂μ :=
          integral_add Ie If
      _ = _ := by rw [hO2, zero_add]
  rw [hstep1, hstep2, hstep3]
  ring

end MainProof

end S_AutomorphicForm_setIntegral_continuousPart_mul_conj_convOp_continuousPart_eq_sub_of_pseudoEisenstein_threeWay
end P2MW
export P2MW.S_AutomorphicForm_setIntegral_continuousPart_mul_conj_convOp_continuousPart_eq_sub_of_pseudoEisenstein_threeWay (solution)
