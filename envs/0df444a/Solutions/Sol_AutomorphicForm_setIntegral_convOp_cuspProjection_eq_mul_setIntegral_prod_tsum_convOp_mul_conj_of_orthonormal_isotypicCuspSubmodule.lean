-- Prove2me | solution 1 for AutomorphicForm.setIntegral_convOp_cuspProjection_eq_mul_setIntegral_prod_tsum_convOp_mul_conj_of_orthonormal_isotypicCuspSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/6503416c-f776-54bb-98b3-fb4645f760b0

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

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Theorems.Thm_AutomorphicForm_hasSum_setIntegral_mul_conj_mul_setIntegral_convOp_of_orthonormal_isotypicCuspSubmodule
import Theorems.Thm_AutomorphicForm_setIntegral_mul_conj_eq_mul_setIntegral_inter_conj_of_lsXi_threeWay_of_mem_isotypicCuspSubmodule
import Theorems.Thm_AutomorphicForm_continuous_convOp_of_isAutomorphicFnAt_canonicalTruncationDomain_of_continuous
import Theorems.Thm_AutomorphicForm_forall_isCompact_exists_summable_forall_finsum_norm_convOp_mul_conj_le_of_orthonormal_isotypicCuspSubmodule
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum

import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setIntegral_convOp_cuspProjection_eq_mul_setIntegral_prod_tsum_convOp_mul_conj_of_orthonormal_isotypicCuspSubmodule
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec"
p2m_attr_erase "simp" "AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed HeckePair.IsGelfandInvolution.reindex_mk HeckePair.IsGelfandInvolution.reindexInv_mk AutomorphicForm.iotaZsqrtdNegTwo_apply LanglandsTunnell.Converse.ArchDatumC.mk.injEq LanglandsTunnell.Converse.ArchDatumC.mk.sizeOf_spec LanglandsTunnell.Converse.FinWhittakerDatum.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.injEq LanglandsTunnell.Converse.FinWhittakerDatum.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.sizeOf_spec LanglandsTunnell.Converse.JLData.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.injEq LanglandsTunnell.Converse.JLData.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul"
p2m_attr_erase "simp" "IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel
open AutomorphicForm

namespace CuspMemberKit

p2m_open "MeasureTheory NumberField AutomorphicForm AutomorphicForm.CuspidalSpectrum~isotypicCuspSubmodule_le_cuspMemberSubmodule"

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

theorem memLp_two_of_isAutomorphicFnAt {Φ₀ : Set (AdelicGL2 (𝓞 K) K)} {ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ}
    {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (h : IsAutomorphicFnAt K (productionPinsOf K Φ₀ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ φ) :
    MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀) :=
  ((isAutomorphicFnAt_fdPins_iff K Φ₀ ξ φ).1 h).2

theorem integrable_mul_conj {μ : Measure (AdelicGL2 (𝓞 K) K)} {a c : AdelicGL2 (𝓞 K) K → ℂ}
    (ha : MemLp a 2 μ) (hc : MemLp c 2 μ) : Integrable (fun g => a g * conj (c g)) μ :=
  ha.integrable_mul hc.star

end CuspMemberKit

section
open scoped ENNReal
namespace CuspRectKit

theorem integral_prod_tsum_mul_eq_tsum_integral_mul_integral
    {X : Type*} [MeasurableSpace X] {ι : Type*} [Countable ι]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (F G : ι → X → ℂ)
    (hF : ∀ i, AEStronglyMeasurable (F i) μ) (hG : ∀ i, AEStronglyMeasurable (G i) ν)
    (Mtot : ℝ)
    (hbound : ∀ᵐ p ∂(μ.prod ν), ∑' i, ‖F i p.1 * G i p.2‖ₑ ≤ ENNReal.ofReal Mtot) :
    ∫ p, (∑' i, F i p.1 * G i p.2) ∂(μ.prod ν) = ∑' i, (∫ x, F i x ∂μ) * (∫ y, G i y ∂ν) := by
  have hmeas : ∀ i, AEStronglyMeasurable (fun p : X × X => F i p.1 * G i p.2) (μ.prod ν) :=
    fun i => ((hF i).comp_fst).mul ((hG i).comp_snd)
  have hsum : ∑' i, ∫⁻ p, ‖F i p.1 * G i p.2‖ₑ ∂(μ.prod ν) ≠ ⊤ := by
    rw [← lintegral_tsum (fun i => (hmeas i).enorm)]
    refine ne_top_of_le_ne_top ?_ (lintegral_mono_ae hbound)
    rw [lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  rw [integral_tsum hmeas hsum]
  congr 1; funext i
  exact integral_prod_mul (F i) (G i)

end CuspRectKit

end

open scoped ENNReal in
p2m_open "AutomorphicForm.CuspidalSpectrum~isotypicCuspSubmodule_le_cuspMemberSubmodule" in open AutomorphicForm  in
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
    ∀ (C : Set (AdelicGL2 (𝓞 K) K)) (_hC : IsCompact C)
      (A : Set (AdelicGL2 (𝓞 K) K)) (_hA : A ⊆ C) (_hAm : MeasurableSet A)
      (B : Set (AdelicGL2 (𝓞 K) K)) (_hB : B ⊆ C) (_hBm : MeasurableSet B)
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
      (_hsum : (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator (B.indicator fun _ => (1 : ℂ))
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) =ᵐ[((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))] uc + ur + ue),
    ∫ x in A, convOp K f uc x ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) =
      ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) *
      ∫ p in A ×ˢ B, (∑' i : ι, convOp K f (b i) p.1 * conj (b i p.2)) ∂(((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)).prod ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))) := by
  intro ι b cls hb hbn hbo hbs hbc f hf hfc hfF hfB hfA C hC A hA hAm B hB hBm uc ur ue huc huc0 hur hurc hue hueo hsum
  letI := adeleBorel (𝓞 K) K
  classical
  haveI hHaar := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  have hαm : ∀ x : (AdeleRing (𝓞 K) K)ˣ, 0 < (((((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits x : ℝˣ) : ℝ)) := by
    intro x
    rw [MonoidHom.coe_toHomUnits]
    exact NNReal.coe_pos.2 distribHaarChar_pos

  have hdat := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ

  have hbmem : ∀ i, b i ∈ AutomorphicForm.CuspidalSpectrum.cuspMemberSubmodule K (AutomorphicForm.canonicalTruncationDomain K α β) ξK :=
    fun i => CuspMemberKit.isotypicCuspSubmodule_le_cuspMemberSubmodule _ ξK N SK (cls i) (Submodule.mem_inf.1 (hb i).2).1
  have hbaut : ∀ i, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK (b i) := fun i => (CuspMemberKit.mem_kit (hbmem i)).1
  have hbcont : ∀ i, Continuous (b i) := fun i => (CuspMemberKit.mem_kit (hbmem i)).2.2.2
  have hFcont : ∀ i, Continuous (convOp K f (b i)) := fun i =>
    AutomorphicForm.continuous_convOp_of_isAutomorphicFnAt_canonicalTruncationDomain_of_continuous K α β hα hαβ ξK hξc
      (b i) (hbaut i) f hf hfc

  have hPX := AutomorphicForm.hasSum_setIntegral_mul_conj_mul_setIntegral_convOp_of_orthonormal_isotypicCuspSubmodule
    K α β hα hαβ ΦK cK uK d₁K d₂K TK hcK hd₁K hdK hcovK νZK ΩK hΩK SK ξK hξc hξt N hN tysK hξu
    ι b cls hb hbn hbo hbs hbc f hf hfc hfF hfB hfA A hAm uc huc huc0

  have hCU := AutomorphicForm.setIntegral_mul_conj_eq_mul_setIntegral_inter_conj_of_lsXi_threeWay_of_mem_isotypicCuspSubmodule
    K α β hα hαβ ΦK cK uK d₁K d₂K TK hcK hd₁K hdK hcovK νZK ΩK hΩK SK ξK hξc hξt N hN tysK hξu
    ι b cls hb C hC B hB hBm uc ur ue huc huc0 hur hurc hue hueo hsum

  set bK : ℂ := ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) with hbK
  set μ₀ : Measure (AdelicGL2 (𝓞 K) K) := (adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β) with hμ₀
  set I : ι → ℂ := fun i => ∫ x in A, convOp K f (b i) x ∂μ₀ with hI
  set J : ι → ℂ := fun i => ∫ y in B, conj (b i y) ∂μ₀ with hJ
  have hJ' : ∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β ∩ B, conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = J i := by
    intro i
    simp only [hJ, hμ₀]
    rw [Measure.restrict_restrict hBm, Set.inter_comm]

  have hLHS : ∫ x in A, convOp K f uc x ∂μ₀ = bK * ∑' i, I i * J i := by
    have h1 : HasSum (fun i => bK * (I i * J i)) (∫ x in A, convOp K f uc x ∂μ₀) := by
      refine HasSum.congr_fun hPX ?_
      intro i
      symm
      show (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, uc g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) * I i = bK * (I i * J i)
      rw [hCU i, hJ' i]; ring
    rw [← h1.tsum_eq, tsum_mul_left]
  rw [hLHS]
  congr 1

  obtain ⟨M, hMs, hMb⟩ :=
    AutomorphicForm.forall_isCompact_exists_summable_forall_finsum_norm_convOp_mul_conj_le_of_orthonormal_isotypicCuspSubmodule
      K α β hα hαβ ΦK cK uK d₁K d₂K TK hcK hd₁K hdK hcovK νZK ΩK hΩK SK ξK hξc hξt N hN tysK hξu hαm
      ι b cls hb hbn hbo hbs hbc f hf hfc hfF hfB hfA C hC
  set F : ι → AdelicGL2 (𝓞 K) K → ℂ := fun i x => convOp K f (b i) x with hF
  set G : ι → AdelicGL2 (𝓞 K) K → ℂ := fun i y => conj (b i y) with hG

  have hfib : ∀ π : HeckeEigensystem K ℂ, {i : ι | cls i = π}.Finite := by
    intro π
    by_cases hne : ∃ i, cls i = π
    · obtain ⟨i, hi⟩ := hne
      have := (hbs π (hi ▸ (hb i).1)).1
      exact this
    · push_neg at hne
      convert Set.finite_empty
      ext i; simp [hne i]
  haveI hfibT : ∀ π : HeckeEigensystem K ℂ, Finite {i : ι // cls i = π} := fun π => (hfib π).to_subtype

  have hterm : ∀ i, ∀ x ∈ C, ∀ y ∈ C, ‖F i x * G i y‖ ≤ M (cls i) := by
    intro i x hx y hy
    have h := hMb (cls i) x hx y hy
    haveI : Fintype {j : ι // cls j = cls i} := Fintype.ofFinite _
    rw [finsum_eq_sum_of_fintype] at h
    refine le_trans ?_ h
    have := Finset.single_le_sum (f := fun j : {j : ι // cls j = cls i} => ‖convOp K f (b j) x * conj (b j y)‖)
      (fun j _ => norm_nonneg _) (Finset.mem_univ ⟨i, rfl⟩)
    simpa [hF, hG] using this
  have hM0 : ∀ i, ∀ x ∈ C, ∀ y ∈ C, M (cls i) = 0 → F i x * G i y = 0 := by
    intro i x hx y hy h0
    have := hterm i x hx y hy
    rw [h0] at this
    exact norm_le_zero_iff.1 this

  set ι' : Set ι := {i | M (cls i) ≠ 0} with hι'
  have hι'c : ι'.Countable := by
    have hsupp : (Function.support M).Countable := hMs.countable_support
    have hsub : ι' ⊆ ⋃ π ∈ Function.support M, {i | cls i = π} := by
      intro i hi
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
      exact ⟨cls i, hi, rfl⟩
    exact (hsupp.biUnion fun π _ => (hfib π).countable).mono hsub
  haveI : Countable ι' := hι'c.to_subtype

  have hΦfin : adelicGLHaar (Fin 2) (𝓞 K) K (AutomorphicForm.canonicalTruncationDomain K α β) < ⊤ := by
    have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain K α β hα hαβ
      (AutomorphicForm.canonicalTruncationDomain K α β) hdat.2.2.2.2
    rwa [Set.inter_eq_left.2 hdat.2.2.2.1] at h
  haveI : IsFiniteMeasure μ₀ := ⟨by rw [hμ₀, Measure.restrict_apply_univ]; exact hΦfin⟩

  have haeAB : ∀ᵐ p ∂((μ₀.restrict A).prod (μ₀.restrict B)), p ∈ A ×ˢ B := by
    rw [Measure.prod_restrict (μ := μ₀) (ν := μ₀) A B]
    exact ae_restrict_mem (hAm.prod hBm)

  have hSred : ∀ p ∈ A ×ˢ B, (∑' i, F i p.1 * G i p.2) = ∑' i : ι', F i p.1 * G i p.2 := by
    intro p hp
    refine (tsum_subtype_eq_of_support_subset ?_).symm
    intro i hi
    by_contra hni
    exact hi (hM0 i p.1 (hA hp.1) p.2 (hB hp.2) (by simpa [hι'] using hni))

  have hIJ0 : ∀ i, M (cls i) = 0 → I i * J i = 0 := by
    intro i h0
    have h1 : I i * J i = ∫ p, F i p.1 * G i p.2 ∂((μ₀.restrict A).prod (μ₀.restrict B)) := by
      rw [integral_prod_mul]
    rw [h1]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [haeAB] with p hp
    exact hM0 i p.1 (hA hp.1) p.2 (hB hp.2) h0
  have hIJred : (∑' i, I i * J i) = ∑' i : ι', I i * J i := by
    refine (tsum_subtype_eq_of_support_subset ?_).symm
    intro i hi
    by_contra hni
    exact hi (hIJ0 i (by simpa [hι'] using hni))

  set Mp : HeckeEigensystem K ℂ → ℝ := fun π => max (M π) 0 with hMp
  have hMp0 : ∀ π, 0 ≤ Mp π := fun π => le_max_right _ _
  have hMps : Summable Mp :=
    Summable.of_nonneg_of_le hMp0 (fun π => by
      show max (M π) 0 ≤ |M π|
      exact max_le (le_abs_self _) (abs_nonneg _)) hMs.abs

  have hFm : ∀ i, AEStronglyMeasurable (F i) (μ₀.restrict A) := fun i => (hFcont i).aestronglyMeasurable
  have hGm : ∀ i, AEStronglyMeasurable (G i) (μ₀.restrict B) := fun i =>
    (Complex.continuous_conj.comp (hbcont i)).aestronglyMeasurable

  have hbound : ∀ᵐ p ∂((μ₀.restrict A).prod (μ₀.restrict B)),
      ∑' i : ι', ‖F i p.1 * G i p.2‖ₑ ≤ ENNReal.ofReal (∑' π, Mp π) := by
    filter_upwards [haeAB] with p hp
    have hx : p.1 ∈ C := hA hp.1
    have hy : p.2 ∈ C := hB hp.2
    calc ∑' i : ι', ‖F i p.1 * G i p.2‖ₑ
        ≤ ∑' i : ι, ‖F i p.1 * G i p.2‖ₑ := ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _
      _ = ∑' q : (π : HeckeEigensystem K ℂ) × {i : ι // cls i = π}, ‖F q.2 p.1 * G q.2 p.2‖ₑ :=
          ((Equiv.sigmaFiberEquiv cls).tsum_eq (fun i => ‖F i p.1 * G i p.2‖ₑ)).symm
      _ = ∑' π : HeckeEigensystem K ℂ, ∑' j : {i : ι // cls i = π}, ‖F j p.1 * G j p.2‖ₑ := ENNReal.tsum_sigma' _
      _ ≤ ∑' π : HeckeEigensystem K ℂ, ENNReal.ofReal (Mp π) := by
          refine ENNReal.tsum_le_tsum fun π => ?_
          haveI : Fintype {i : ι // cls i = π} := Fintype.ofFinite _
          rw [tsum_fintype]
          have h := hMb π p.1 hx p.2 hy
          rw [finsum_eq_sum_of_fintype] at h
          calc ∑ j : {i : ι // cls i = π}, ‖F j p.1 * G j p.2‖ₑ
              = ENNReal.ofReal (∑ j : {i : ι // cls i = π}, ‖F j p.1 * G j p.2‖) := by
                  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => norm_nonneg _)]
                  congr 1; funext j; exact (ofReal_norm_eq_enorm _).symm
            _ ≤ ENNReal.ofReal (Mp π) := by
                  refine ENNReal.ofReal_le_ofReal (le_trans ?_ (le_max_left _ _))
                  simpa [hF, hG] using h
      _ = ENNReal.ofReal (∑' π, Mp π) := (ENNReal.ofReal_tsum_of_nonneg hMp0 hMps).symm

  have hswap := CuspRectKit.integral_prod_tsum_mul_eq_tsum_integral_mul_integral (μ₀.restrict A) (μ₀.restrict B)
    (fun i : ι' => F i) (fun i : ι' => G i) (fun i => hFm i) (fun i => hGm i) _ hbound

  rw [hIJred]
  symm
  calc ∫ p in A ×ˢ B, (∑' i, convOp K f (b i) p.1 * conj (b i p.2)) ∂(μ₀.prod μ₀)
      = ∫ p, (∑' i, F i p.1 * G i p.2) ∂((μ₀.restrict A).prod (μ₀.restrict B)) := by
          rw [Measure.prod_restrict (μ := μ₀) (ν := μ₀) A B]
    _ = ∫ p, (∑' i : ι', F i p.1 * G i p.2) ∂((μ₀.restrict A).prod (μ₀.restrict B)) := by
          refine integral_congr_ae ?_
          filter_upwards [haeAB] with p hp
          exact hSred p hp
    _ = ∑' i : ι', (∫ x, F i x ∂(μ₀.restrict A)) * (∫ y, G i y ∂(μ₀.restrict B)) := hswap
    _ = ∑' i : ι', I i * J i := rfl

end S_AutomorphicForm_setIntegral_convOp_cuspProjection_eq_mul_setIntegral_prod_tsum_convOp_mul_conj_of_orthonormal_isotypicCuspSubmodule
end P2MW
export P2MW.S_AutomorphicForm_setIntegral_convOp_cuspProjection_eq_mul_setIntegral_prod_tsum_convOp_mul_conj_of_orthonormal_isotypicCuspSubmodule (solution)
