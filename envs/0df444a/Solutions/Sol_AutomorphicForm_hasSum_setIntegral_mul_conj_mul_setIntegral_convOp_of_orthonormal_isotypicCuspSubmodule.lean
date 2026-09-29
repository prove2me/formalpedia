-- Prove2me | solution 1 for AutomorphicForm.hasSum_setIntegral_mul_conj_mul_setIntegral_convOp_of_orthonormal_isotypicCuspSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/d30a61d5-daf7-5bcd-b07d-a7d571082dd4

import Theorems.Thm_AutomorphicForm_convOp_ae_eq_zero_restrict_canonicalTruncationDomain_of_ae_constantTerm_eq_zero_of_forall_setIntegral_mul_conj_eq_zero
import Theorems.Thm_AutomorphicForm_exists_isAutomorphicFnAt_ae_eq_of_tendsto_eLpNorm_and_ae_constantTerm_eq_zero_canonicalTruncationDomain
import Theorems.Thm_Orthonormal_hasSum_inner_smul_map_of_map_eq_zero_of_forall_inner_eq_zero
import Theorems.Thm_AutomorphicForm_exists_forall_eLpNorm_convOp_le_mul_eLpNorm_restrict_canonicalTruncationDomain_of_isAutomorphicFnAt
import Theorems.Thm_AutomorphicForm_convOp_eq_add_add_of_ae_eq_restrict_canonicalTruncationDomain_of_isAutomorphicFnAt_of_continuous
import Theorems.Thm_AutomorphicForm_isAutomorphicFnAt_convOp_of_isAutomorphicFnAt_canonicalTruncationDomain
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_hasSum_setIntegral_mul_conj_mul_setIntegral_convOp_of_orthonormal_isotypicCuspSubmodule
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec"
p2m_attr_erase "simp" "AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed HeckePair.IsGelfandInvolution.reindex_mk HeckePair.IsGelfandInvolution.reindexInv_mk"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal ENNReal InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open AutomorphicForm

noncomputable section

abbrev PE.pins (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))] (α β : ℝ) :
    CarrierPins K :=
  productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
    (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)

namespace PE

private abbrev _root_.PE.ν (K : Type) [Field K] [NumberField K] (α β : ℝ) : Measure (AdelicGL2 (𝓞 K) K) :=
  (adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)

end PE
p2m_export "" "PE.ν"
section Algebra
variable (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))] (α β : ℝ)
  (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)

theorem PE.aut_iff (φ : AdelicGL2 (𝓞 K) K → ℂ) :
    IsAutomorphicFnAt K (PE.pins K α β) ξ φ ↔ IsLsXiFunction (𝓞 K) K ⊤ ξ φ ∧ MemLp φ 2 (PE.ν K α β) :=
  lsXiMemberAt_iff _ _ _ _ _ _ _

theorem PE.aut_add {v w : AdelicGL2 (𝓞 K) K → ℂ} (hv : IsAutomorphicFnAt K (PE.pins K α β) ξ v)
    (hw : IsAutomorphicFnAt K (PE.pins K α β) ξ w) : IsAutomorphicFnAt K (PE.pins K α β) ξ (v + w) := by
  rw [PE.aut_iff] at hv hw ⊢
  refine ⟨⟨fun γ g => ?_, fun z g => ?_⟩, hv.2.add hw.2⟩
  · simp only [Pi.add_apply, hv.1.left_invariant, hw.1.left_invariant]
  · simp only [Pi.add_apply, hv.1.central_transform, hw.1.central_transform, mul_add]

theorem PE.aut_smul (c : ℂ) {v : AdelicGL2 (𝓞 K) K → ℂ} (hv : IsAutomorphicFnAt K (PE.pins K α β) ξ v) :
    IsAutomorphicFnAt K (PE.pins K α β) ξ (c • v) := by
  rw [PE.aut_iff] at hv ⊢
  refine ⟨⟨fun γ g => ?_, fun z g => ?_⟩, hv.2.const_smul c⟩
  · simp only [Pi.smul_apply, hv.1.left_invariant]
  · simp only [Pi.smul_apply, hv.1.central_transform, smul_eq_mul]; ring

theorem PE.aut_sub {v w : AdelicGL2 (𝓞 K) K → ℂ} (hv : IsAutomorphicFnAt K (PE.pins K α β) ξ v)
    (hw : IsAutomorphicFnAt K (PE.pins K α β) ξ w) : IsAutomorphicFnAt K (PE.pins K α β) ξ (v - w) := by
  have h := PE.aut_add K α β ξ hv (PE.aut_smul K α β ξ (-1) hw)
  have heq : v + (-1 : ℂ) • w = v - w := by funext g; simp [sub_eq_add_neg]
  rwa [heq] at h

theorem PE.aut_zero : IsAutomorphicFnAt K (PE.pins K α β) ξ (0 : AdelicGL2 (𝓞 K) K → ℂ) :=
  isAutomorphicFnAt_zero K (PE.pins K α β) ξ

theorem PE.inner_eq (φ ψ : Lp ℂ 2 (PE.ν K α β)) (v w : AdelicGL2 (𝓞 K) K → ℂ)
    (hv : (φ : AdelicGL2 (𝓞 K) K → ℂ) =ᵐ[PE.ν K α β] v) (hw : (ψ : AdelicGL2 (𝓞 K) K → ℂ) =ᵐ[PE.ν K α β] w) :
    ⟪ψ, φ⟫_ℂ = ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, v g * conj (w g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hv, hw] with g hgv hgw
  rw [RCLike.inner_apply, hgv, hgw]

end Algebra

namespace CuspMemberKit
open AutomorphicForm.CuspidalSpectrum
variable {K : Type} [Field K] [NumberField K]

theorem isotypicCuspSubmodule_le_cuspMemberSubmodule (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (π : HeckeEigensystem K ℂ) :
    isotypicCuspSubmodule K (productionPinsOf K Φ₀ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S π ≤ cuspMemberSubmodule K Φ₀ ξ :=
  Submodule.span_le.2 fun _ ha => ⟨ha.smoothCusp, ha.continuous⟩

theorem mem_kit {Φ₀ : Set (AdelicGL2 (𝓞 K) K)} {ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (h : φ ∈ cuspMemberSubmodule K Φ₀ ξ) :
    IsAutomorphicFnAt K (productionPinsOf K Φ₀ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ φ ∧
      MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀) ∧
      @IsCuspidalFn _ (productionPinsOf K Φ₀ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
        (productionPinsOf K Φ₀ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν unipotentGL2 φ ∧ Continuous φ :=
  ⟨h.1.1.1, ((isAutomorphicFnAt_fdPins_iff K Φ₀ ξ φ).1 h.1.1.1).2, h.1.1.2, h.2⟩

end CuspMemberKit

end

theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1) :
    letI := adeleBorel (𝓞 K) K
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
      (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f),
      IsFactorizableTestFn K f →
      IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f →
      IsArchBiFinite K tysK f →
    ∀ (A : Set (AdelicGL2 (𝓞 K) K)) (_hAm : MeasurableSet A)
      (u : AdelicGL2 (𝓞 K) K → ℂ)
      (_hu : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u) (_hu0 : (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 u g = 0)),
    HasSum (fun i : ι => (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, u g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
        ∫ x in A, convOp K f (b i) x ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)))
      (∫ x in A, convOp K f u x ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))) := by
  intro ι b cls hb hbn hbo hbs hbc f _hf _hfc hfact hbi harch A _hAm u _hu _hu0
  classical
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := adeleBorel (𝓞 K) K
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K

  obtain ⟨-, -, -, hslab, hFD⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ
  have hfin : adelicGLHaar (Fin 2) (𝓞 K) K (AutomorphicForm.canonicalTruncationDomain K α β) < ⊤ := by
    have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain K α β hα hαβ
      (AutomorphicForm.canonicalTruncationDomain K α β) hFD
    rwa [Set.inter_eq_left.mpr hslab] at h
  haveI hνfin : IsFiniteMeasure (PE.ν K α β) := isFiniteMeasure_restrict.2 hfin.ne

  obtain ⟨hComplete, hClosed, hCTlin⟩ :=
    AutomorphicForm.exists_isAutomorphicFnAt_ae_eq_of_tendsto_eLpNorm_and_ae_constantTerm_eq_zero_canonicalTruncationDomain
      K α β hα hαβ ξK hξc hξu

  have hkit : ∀ i, IsAutomorphicFnAt K (PE.pins K α β) ξK (b i) ∧ MemLp (b i) 2 (PE.ν K α β) ∧
      (∀ g, constantTerm (PE.pins K α β).ν unipotentGL2 (b i) g = 0) ∧ Continuous (b i) := by
    intro i
    have h := CuspMemberKit.mem_kit
      (CuspMemberKit.isotypicCuspSubmodule_le_cuspMemberSubmodule _ ξK N SK (cls i) (hb i).2.1)
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  have huM : MemLp u 2 (PE.ν K α β) := ((PE.aut_iff K α β ξK u).1 _hu).2

  set eb : ι → Lp ℂ 2 (PE.ν K α β) := fun i => (hkit i).2.1.toLp (b i) with heb
  set eu : Lp ℂ 2 (PE.ν K α β) := huM.toLp u with heu
  have heb_ae : ∀ i, (eb i : AdelicGL2 (𝓞 K) K → ℂ) =ᵐ[PE.ν K α β] b i := fun i => MemLp.coeFn_toLp _
  have heu_ae : (eu : AdelicGL2 (𝓞 K) K → ℂ) =ᵐ[PE.ν K α β] u := MemLp.coeFn_toLp _
  have horth : Orthonormal ℂ eb := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [PE.inner_eq K α β (eb j) (eb i) (b j) (b i) (heb_ae j) (heb_ae i)]
    split_ifs with hij
    · subst hij; exact hbn i
    · exact hbo j i (Ne.symm hij)
  have hcoef : ∀ i, ⟪eb i, eu⟫_ℂ =
      ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, u g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
    fun i => PE.inner_eq K α β eu (eb i) u (b i) heu_ae (heb_ae i)

  let S : Submodule ℂ (Lp ℂ 2 (PE.ν K α β)) :=
    { carrier := {φ | ∃ v : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (PE.pins K α β) ξK v ∧
        (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (PE.pins K α β).ν unipotentGL2 v g = 0) ∧
        (φ : AdelicGL2 (𝓞 K) K → ℂ) =ᵐ[PE.ν K α β] v}
      zero_mem' := ⟨0, PE.aut_zero K α β ξK,
        Filter.Eventually.of_forall fun g => constantTerm_zero _ _ g, Lp.coeFn_zero _ _ _⟩
      add_mem' := by
        rintro φ ψ ⟨v, hv, hvc, hφv⟩ ⟨w, hw, hwc, hψw⟩
        refine ⟨v + w, PE.aut_add K α β ξK hv hw, ?_, (Lp.coeFn_add φ ψ).trans (hφv.add hψw)⟩
        have h := hCTlin v w 1 1 hv hw hvc hwc
        have heq : (fun g => (1 : ℂ) * v g + 1 * w g) = v + w := by funext g; simp only [one_mul, Pi.add_apply]
        rwa [heq] at h
      smul_mem' := by
        rintro c φ ⟨v, hv, hvc, hφv⟩
        refine ⟨c • v, PE.aut_smul K α β ξK c hv, ?_,
          (Lp.coeFn_smul c φ).trans (hφv.mono fun g hg => by simp only [Pi.smul_apply, hg])⟩
        have h := hCTlin v v c 0 hv hv hvc hvc
        have heq : (fun g => c * v g + 0 * v g) = c • v := by
          funext g; simp only [zero_mul, add_zero, Pi.smul_apply, smul_eq_mul]
        rwa [heq] at h }
  have hSmem : ∀ φ : Lp ℂ 2 (PE.ν K α β), φ ∈ S ↔ ∃ v : AdelicGL2 (𝓞 K) K → ℂ,
      IsAutomorphicFnAt K (PE.pins K α β) ξK v ∧
        (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (PE.pins K α β).ν unipotentGL2 v g = 0) ∧
        (φ : AdelicGL2 (𝓞 K) K → ℂ) =ᵐ[PE.ν K α β] v := fun φ => Iff.rfl
  have hSclosed : IsClosed (S : Set (Lp ℂ 2 (PE.ν K α β))) := by
    refine IsSeqClosed.isClosed ?_
    intro x xlim hx hconv
    have hx' : ∀ n, ∃ v : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (PE.pins K α β) ξK v ∧
        (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (PE.pins K α β).ν unipotentGL2 v g = 0) ∧
        ((x n : Lp ℂ 2 _) : AdelicGL2 (𝓞 K) K → ℂ) =ᵐ[PE.ν K α β] v := fun n => hx n
    choose v hv hvc hxv using hx'
    have h1 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' x xlim).1 hconv
    have h2 : Filter.Tendsto (fun n => eLpNorm (v n - (xlim : AdelicGL2 (𝓞 K) K → ℂ)) 2 (PE.ν K α β))
        Filter.atTop (nhds 0) := by
      refine (Filter.tendsto_congr fun n => ?_).1 h1
      exact eLpNorm_congr_ae ((hxv n).sub Filter.EventuallyEq.rfl)
    obtain ⟨U, hU, hUx⟩ := hComplete v xlim hv (Lp.memLp xlim) h2
    have h3 : Filter.Tendsto (fun n => eLpNorm (v n - U) 2 (PE.ν K α β)) Filter.atTop (nhds 0) := by
      refine (Filter.tendsto_congr fun n => ?_).1 h2
      exact eLpNorm_congr_ae (Filter.EventuallyEq.rfl.sub hUx.symm)
    exact ⟨U, hU, hClosed v U hv hvc hU h3, hUx.symm⟩

  set V : Submodule ℂ (Lp ℂ 2 (PE.ν K α β)) := (Submodule.span ℂ (Set.range eb)).topologicalClosure with hV
  have hebS : ∀ i, eb i ∈ S := fun i =>
    ⟨b i, (hkit i).1, Filter.Eventually.of_forall (hkit i).2.2.1, heb_ae i⟩
  have hVS : V ≤ S :=
    Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hebS i)) hSclosed
  have hebV : ∀ i, eb i ∈ V := fun i =>
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, rfl⟩)
  have hVclosed : IsClosed (V : Set (Lp ℂ 2 (PE.ν K α β))) := Submodule.isClosed_topologicalClosure _
  haveI : CompleteSpace V := hVclosed.completeSpace_coe

  set p : V := V.orthogonalProjection eu with hp
  obtain ⟨pt, hptA, hptC, hpt_ae⟩ := (hSmem _).1 (hVS p.2)
  have hptM : MemLp pt 2 (PE.ν K α β) := ((PE.aut_iff K α β ξK pt).1 hptA).2
  have hp_eq : (p : Lp ℂ 2 (PE.ν K α β)) = hptM.toLp pt := by
    rw [← Lp.toLp_coeFn (p : Lp ℂ 2 (PE.ν K α β)) (Lp.memLp _)]
    exact MemLp.toLp_congr _ _ hpt_ae

  set v : AdelicGL2 (𝓞 K) K → ℂ := u - pt with hvdef
  have hvA : IsAutomorphicFnAt K (PE.pins K α β) ξK v := PE.aut_sub K α β ξK _hu hptA
  have hvM : MemLp v 2 (PE.ν K α β) := ((PE.aut_iff K α β ξK v).1 hvA).2
  have hvC : ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (PE.pins K α β).ν unipotentGL2 v g = 0 := by
    have h := hCTlin u pt 1 (-1) _hu hptA _hu0 hptC
    have heq : (fun g => (1 : ℂ) * u g + (-1) * pt g) = v := by
      funext g; simp only [hvdef, Pi.sub_apply]; ring
    rwa [heq] at h
  have hv_toLp : hvM.toLp v = eu - (p : Lp ℂ 2 (PE.ν K α β)) := by
    rw [hp_eq, heu, ← MemLp.toLp_sub]
  have hvo : ∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, v g * conj (b i g)
      ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 := by
    intro i
    rw [← PE.inner_eq K α β (hvM.toLp v) (eb i) v (b i) (MemLp.coeFn_toLp _) (heb_ae i), hv_toLp]
    exact Submodule.inner_right_of_mem_orthogonal (hebV i) (Submodule.sub_starProjection_mem_orthogonal eu)
  have hRv0 : convOp K f v =ᵐ[PE.ν K α β] 0 :=
    AutomorphicForm.convOp_ae_eq_zero_restrict_canonicalTruncationDomain_of_ae_constantTerm_eq_zero_of_forall_setIntegral_mul_conj_eq_zero
      K α β hα hαβ ΦK cK uK d₁K d₂K TK hcK hd₁K hdK hcovK νZK ΩK hΩK SK ξK hξc hξt N hN tysK hξu
      ι b cls hb hbs hbc f _hf _hfc hfact hbi harch v hvA hvC hvo

  have hWD : ∀ q₁ q₂ : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (PE.pins K α β) ξK q₁ →
      IsAutomorphicFnAt K (PE.pins K α β) ξK q₂ → q₁ =ᵐ[PE.ν K α β] q₂ →
      ∀ x, convOp K f q₁ x = convOp K f q₂ x := by
    intro q₁ q₂ h₁ h₂ h12 x
    have h := AutomorphicForm.convOp_eq_add_add_of_ae_eq_restrict_canonicalTruncationDomain_of_isAutomorphicFnAt_of_continuous
      K α β hα hαβ ξK hξc q₁ q₂ 0 0 h₁ h₂ (PE.aut_zero K α β ξK) (PE.aut_zero K α β ξK)
      (by simpa only [add_zero] using h12) f _hf _hfc x
    simpa only [convOp_zero, Pi.zero_apply, add_zero] using h
  have hADD : ∀ q₁ q₂ : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (PE.pins K α β) ξK q₁ →
      IsAutomorphicFnAt K (PE.pins K α β) ξK q₂ →
      ∀ x, convOp K f (q₁ + q₂) x = convOp K f q₁ x + convOp K f q₂ x := by
    intro q₁ q₂ h₁ h₂ x
    have h := AutomorphicForm.convOp_eq_add_add_of_ae_eq_restrict_canonicalTruncationDomain_of_isAutomorphicFnAt_of_continuous
      K α β hα hαβ ξK hξc (q₁ + q₂) q₁ q₂ 0 (PE.aut_add K α β ξK h₁ h₂) h₁ h₂ (PE.aut_zero K α β ξK)
      (by simp only [add_zero]; exact Filter.EventuallyEq.rfl) f _hf _hfc x
    simpa only [convOp_zero, Pi.zero_apply, add_zero] using h
  have hRM : ∀ q : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (PE.pins K α β) ξK q →
      MemLp (convOp K f q) 2 (PE.ν K α β) := fun q hq =>
    ((PE.aut_iff K α β ξK _).1 (AutomorphicForm.isAutomorphicFnAt_convOp_of_isAutomorphicFnAt_canonicalTruncationDomain
      K α β hα hαβ ξK hξc hξu q hq f _hf _hfc)).2
  have hINT : ∀ q : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (PE.pins K α β) ξK q →
      Integrable (convOp K f q) ((PE.ν K α β).restrict A) := fun q hq =>
    ((hRM q hq).restrict A).integrable one_le_two

  obtain ⟨cR, hcR0, hcR⟩ :=
    AutomorphicForm.exists_forall_eLpNorm_convOp_le_mul_eLpNorm_restrict_canonicalTruncationDomain_of_isAutomorphicFnAt
      K α β hα hαβ ξK hξc hξu f _hf _hfc

  have hrep : ∀ q : V, ∃ r : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (PE.pins K α β) ξK r ∧
      (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (PE.pins K α β).ν unipotentGL2 r g = 0) ∧
      ((q : Lp ℂ 2 (PE.ν K α β)) : AdelicGL2 (𝓞 K) K → ℂ) =ᵐ[PE.ν K α β] r := fun q => (hSmem _).1 (hVS q.2)
  choose rep hrepA hrepC hrep_ae using hrep
  have hT_wd : ∀ (q : V) (r : AdelicGL2 (𝓞 K) K → ℂ), IsAutomorphicFnAt K (PE.pins K α β) ξK r →
      ((q : Lp ℂ 2 (PE.ν K α β)) : AdelicGL2 (𝓞 K) K → ℂ) =ᵐ[PE.ν K α β] r →
      (∫ x in A, convOp K f (rep q) x ∂(PE.ν K α β)) = ∫ x in A, convOp K f r x ∂(PE.ν K α β) := by
    intro q r hr hqr
    exact integral_congr_ae (Filter.Eventually.of_forall fun x =>
      hWD _ _ (hrepA q) hr ((hrep_ae q).symm.trans hqr) x)
  have hT_add : ∀ q₁ q₂ : V, (∫ x in A, convOp K f (rep (q₁ + q₂)) x ∂(PE.ν K α β)) =
      (∫ x in A, convOp K f (rep q₁) x ∂(PE.ν K α β)) + ∫ x in A, convOp K f (rep q₂) x ∂(PE.ν K α β) := by
    intro q₁ q₂
    have h12 : (((q₁ + q₂ : V) : Lp ℂ 2 (PE.ν K α β)) : AdelicGL2 (𝓞 K) K → ℂ) =ᵐ[PE.ν K α β] rep q₁ + rep q₂ := by
      rw [Submodule.coe_add]
      exact (Lp.coeFn_add _ _).trans ((hrep_ae q₁).add (hrep_ae q₂))
    rw [hT_wd (q₁ + q₂) (rep q₁ + rep q₂) (PE.aut_add K α β ξK (hrepA q₁) (hrepA q₂)) h12,
      integral_congr_ae (Filter.Eventually.of_forall fun x => hADD _ _ (hrepA q₁) (hrepA q₂) x)]
    exact integral_add (hINT _ (hrepA q₁)) (hINT _ (hrepA q₂))
  have hT_smul : ∀ (c : ℂ) (q : V), (∫ x in A, convOp K f (rep (c • q)) x ∂(PE.ν K α β)) =
      c * ∫ x in A, convOp K f (rep q) x ∂(PE.ν K α β) := by
    intro c q
    have h : (((c • q : V) : Lp ℂ 2 (PE.ν K α β)) : AdelicGL2 (𝓞 K) K → ℂ) =ᵐ[PE.ν K α β] c • rep q := by
      rw [Submodule.coe_smul]
      exact (Lp.coeFn_smul _ _).trans ((hrep_ae q).mono fun g hg => by rw [Pi.smul_apply, Pi.smul_apply, hg])
    rw [hT_wd (c • q) (c • rep q) (PE.aut_smul K α β ξK c (hrepA q)) h, convOp_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact integral_const_mul c _
  let Tlin : V →ₗ[ℂ] ℂ :=
    { toFun := fun q => ∫ x in A, convOp K f (rep q) x ∂(PE.ν K α β)
      map_add' := hT_add
      map_smul' := fun c q => by rw [RingHom.id_apply, smul_eq_mul]; exact hT_smul c q }
  have hTlin_apply : ∀ q : V, Tlin q = ∫ x in A, convOp K f (rep q) x ∂(PE.ν K α β) := fun q => rfl

  have hAν : (PE.ν K α β) A ≠ ⊤ := (measure_lt_top _ _).ne
  have hT_bd : ∀ q : V, ‖Tlin q‖ ≤ (‖indicatorConstLp 2 _hAm hAν (1 : ℂ)‖ * cR) * ‖q‖ := by
    intro q
    rw [hTlin_apply]
    have hG := hRM _ (hrepA q)
    have h1 : (∫ x in A, convOp K f (rep q) x ∂(PE.ν K α β)) =
        ⟪indicatorConstLp 2 _hAm hAν (1 : ℂ), hG.toLp (convOp K f (rep q))⟫_ℂ := by
      rw [MeasureTheory.L2.inner_indicatorConstLp_one]
      exact (integral_congr_ae (ae_restrict_of_ae (MemLp.coeFn_toLp hG))).symm
    rw [h1]
    refine (norm_inner_le_norm _ _).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [Lp.norm_toLp, Submodule.coe_norm, Lp.norm_def]
    have hq : eLpNorm (rep q) 2 (PE.ν K α β) = eLpNorm ((q : Lp ℂ 2 (PE.ν K α β)) : AdelicGL2 (𝓞 K) K → ℂ) 2 (PE.ν K α β) :=
      eLpNorm_congr_ae (hrep_ae q).symm
    have hle := (hcR (rep q) (hrepA q)).trans_eq (by rw [hq])
    have hfin' : ENNReal.ofReal cR * eLpNorm ((q : Lp ℂ 2 (PE.ν K α β)) : AdelicGL2 (𝓞 K) K → ℂ) 2 (PE.ν K α β) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top _)
    refine (ENNReal.toReal_mono hfin' hle).trans ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hcR0]
  set Tc : V →L[ℂ] ℂ := Tlin.mkContinuous _ hT_bd with hTc
  have hTc_apply : ∀ q : V, Tc q = ∫ x in A, convOp K f (rep q) x ∂(PE.ν K α β) := fun q => by
    rw [hTc, LinearMap.mkContinuous_apply]
    exact hTlin_apply q
  set T : Lp ℂ 2 (PE.ν K α β) →L[ℂ] ℂ := Tc.comp V.orthogonalProjection with hT

  have hT0 : ∀ w : Lp ℂ 2 (PE.ν K α β), (∀ i, ⟪eb i, w⟫_ℂ = 0) → T w = 0 := by
    intro w hw
    have hwV : w ∈ Vᗮ := by
      rw [hV, Submodule.orthogonal_closure, Submodule.mem_orthogonal]
      intro y hy
      refine Submodule.span_induction (p := fun y _ => ⟪y, w⟫_ℂ = 0) ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨i, rfl⟩; exact hw i
      · exact inner_zero_left _
      · intro y₁ y₂ _ _ h₁ h₂; rw [inner_add_left, h₁, h₂, add_zero]
      · intro c y _ h; rw [inner_smul_left, h, mul_zero]
    rw [hT, ContinuousLinearMap.comp_apply, (Submodule.orthogonalProjection_eq_zero_iff).2 hwV, map_zero]

  have hH := Orthonormal.hasSum_inner_smul_map_of_map_eq_zero_of_forall_inner_eq_zero eb horth T hT0 eu

  have hTeb : ∀ i, T (eb i) = ∫ x in A, convOp K f (b i) x ∂(PE.ν K α β) := by
    intro i
    rw [hT, ContinuousLinearMap.comp_apply]
    have : V.orthogonalProjection (eb i) = ⟨eb i, hebV i⟩ :=
      Submodule.orthogonalProjection_mem_subspace_eq_self (⟨eb i, hebV i⟩ : V)
    rw [this, hTc_apply]
    exact hT_wd _ (b i) (hkit i).1 (heb_ae i)
  have hTeu : T eu = ∫ x in A, convOp K f u x ∂(PE.ν K α β) := by
    rw [hT, ContinuousLinearMap.comp_apply, hTc_apply, hT_wd p pt hptA hpt_ae]
    have hu_split : u = pt + v := by rw [hvdef, add_sub_cancel]
    have h1 : (∫ x in A, convOp K f u x ∂(PE.ν K α β)) =
        (∫ x in A, convOp K f pt x ∂(PE.ν K α β)) + ∫ x in A, convOp K f v x ∂(PE.ν K α β) := by
      rw [← integral_add (hINT _ hptA) (hINT _ hvA)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show convOp K f u x = convOp K f pt x + convOp K f v x
      conv_lhs => rw [hu_split]
      exact hADD _ _ hptA hvA x
    have h2 : (∫ x in A, convOp K f v x ∂(PE.ν K α β)) = 0 := by
      rw [integral_congr_ae (ae_restrict_of_ae hRv0)]
      simp
    rw [h1, h2, add_zero]
  have key : (fun i => ⟪eb i, eu⟫_ℂ • T (eb i)) = fun i =>
      (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, u g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
        ∫ x in A, convOp K f (b i) x ∂(PE.ν K α β) := by
    funext i; rw [hcoef, hTeb, smul_eq_mul]
  rw [key, hTeu] at hH
  exact hH

end S_AutomorphicForm_hasSum_setIntegral_mul_conj_mul_setIntegral_convOp_of_orthonormal_isotypicCuspSubmodule
end P2MW
export P2MW.S_AutomorphicForm_hasSum_setIntegral_mul_conj_mul_setIntegral_convOp_of_orthonormal_isotypicCuspSubmodule (solution)
