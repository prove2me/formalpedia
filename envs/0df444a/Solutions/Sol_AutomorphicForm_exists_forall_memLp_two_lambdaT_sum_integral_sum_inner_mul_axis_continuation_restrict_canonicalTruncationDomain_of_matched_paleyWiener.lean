-- Prove2me | solution 1 for AutomorphicForm.exists_forall_memLp_two_lambdaT_sum_integral_sum_inner_mul_axis_continuation_restrict_canonicalTruncationDomain_of_matched_paleyWiener
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/f70969ee-c4bd-5b82-b4c1-07e8ff3a9b78

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
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Theorems.Thm_MeasureTheory_memLp_two_integral_and_integral_norm_sq_integral_le_of_integral_norm_sq_le_of_integrable_one_add_sq_mul
import Theorems.Thm_AutomorphicForm_lambdaT_sum_integral_sum_inner_mul_axis_continuation_eq_sum_integral_sum_inner_mul_lambdaT_of_mem_canonicalTruncationDomain_of_matched_paleyWiener
import Theorems.Thm_AutomorphicForm_forall_exists_setIntegral_norm_sq_lambdaT_axis_continuation_le_mul_mul_pow_of_isArchCompAt_of_ne_bot
import Theorems.Thm_AutomorphicForm_continuous_and_integrable_and_memLp_two_integral_mul_conj_flat_section_of_matched_paleyWiener
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Theorems.Thm_LanglandsTunnell_Converse_exists_isArchCompAt_of_isReal
import Theorems.Thm_LanglandsTunnell_Converse_exists_isArchCompAt_of_isComplex
import Theorems.Thm_AutomorphicForm_memLp_two_lambdaT_and_tendsto_eLpNorm_lambdaT_sub_restrict_canonicalTruncationDomain_of_axis_continuation_family
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_memLp_two_lambdaT_sum_integral_sum_inner_mul_axis_continuation_restrict_canonicalTruncationDomain_of_matched_paleyWiener
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite"
p2m_attr_erase "simp" "UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.CuspidalConstituent.rightRegular_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne"
p2m_attr_erase "simp" "NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace Ws48
namespace TPL
open MeasureTheory
theorem norm_sum_mul_sq_le {n : ℕ} (a b : Fin n → ℂ) :
    ‖∑ j, a j * b j‖ ^ 2 ≤ (∑ j, ‖a j‖ ^ 2) * (∑ j, ‖b j‖ ^ 2) := by
  have h1 : ‖∑ j, a j * b j‖ ≤ ∑ j, ‖a j‖ * ‖b j‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (norm_mul_le _ _))
  calc ‖∑ j, a j * b j‖ ^ 2 ≤ (∑ j, ‖a j‖ * ‖b j‖) ^ 2 := by gcongr
    _ ≤ (∑ j, ‖a j‖ ^ 2) * (∑ j, ‖b j‖ ^ 2) := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
end Ws48.TPL

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open AutomorphicForm
open scoped ENNReal

set_option maxHeartbeats 4000000 in
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
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
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
      (_hψK : ∀ e s, IsArchKFinite K (ψf e s)) (_hψsm : ∀ e s, IsKfSmooth K (ψf e s))
      (_hψKu : ∀ (e : ιP) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => ψf e s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
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
      (_hψlev : ∀ i (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf i s (g * u) = ψf i s g)
      (_hψty : ∀ i (s : ℂ), ψf i s ∈ archCutSubmodule K tysK),
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      MemLp (fun x : AdelicGL2 (𝓞 K) K =>
          ∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)), (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
                ∂(maximalCompactHaar K)) *
            @AutomorphicForm.lambdaT _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).nS _ _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν
          (fun n => AutomorphicForm.unipotentGL2 n) (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
          (EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I)) x) 2
        ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ∧
      (∀ x ∈ AutomorphicForm.canonicalTruncationDomain K α β,
        @AutomorphicForm.lambdaT _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).nS _ _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν
          (fun n => AutomorphicForm.unipotentGL2 n) (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
          (fun g : AdelicGL2 (𝓞 K) K =>
            ∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)), (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
                ∂(maximalCompactHaar K)) * EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g) x =
          ∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)), (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
                ∂(maximalCompactHaar K)) *
            @AutomorphicForm.lambdaT _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).nS _ _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν
          (fun n => AutomorphicForm.unipotentGL2 n) (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
          (EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I)) x) ∧
      MemLp (fun x : AdelicGL2 (𝓞 K) K =>
          @AutomorphicForm.lambdaT _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).nS _ _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν
          (fun n => AutomorphicForm.unipotentGL2 n) (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
          (fun g : AdelicGL2 (𝓞 K) K =>
            ∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)), (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
                ∂(maximalCompactHaar K)) * EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g) x) 2
        ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := by
  intro αm hαm ι b cls hb hbn hbo hbs hbc ιE _iC μ ν _hμE _hνE _hμicE _hνicE _hμcE _hνcE _hμν _hdistE nE φE _hφE _hφEK _hφEf _hφEjc _hφEhol _hφEKu _hφEflat _hφElev _hφEty _hφEon _hφEspan _hpairs OE EE NE _hEE ιP _iP μP νP _hμP _hνP _hμicP _hνicP _hμcP _hμνP rP _hr _hdistP ψf _hψf _hψjc _hψhol _hψK _hψsm _hψKu _hνcP _hψdec ψ _hψ _hψrep em τ _hem _hψlev _hψty
  classical
  letI hMSA : MeasurableSpace (AdeleRing (𝓞 K) K) := NumberField.AdelicHaar.adeleBorel (𝓞 K) K
  haveI := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 K) K
  have hNbot : N ≠ ⊥ := by
    intro hN0
    have hall : ∀ w : HeightOneSpectrum (𝓞 K), w ∈ SK := fun w => hN w (by
      rw [hN0, ← Ideal.zero_eq_bot]; exact dvd_zero _)
    have hinj : Function.Injective (algebraMap ℤ (𝓞 K)) := RingHom.injective_int _
    have key : ∀ p : {p : ℕ // p.Prime}, ∃ w : HeightOneSpectrum (𝓞 K),
        w.asIdeal.comap (algebraMap ℤ (𝓞 K)) = Ideal.span {((p : ℕ) : ℤ)} := by
      intro p
      have hp0 : ((p : ℕ) : ℤ) ≠ 0 := by exact_mod_cast p.2.ne_zero
      haveI : (Ideal.span {((p : ℕ) : ℤ)}).IsPrime :=
        (Ideal.span_singleton_prime hp0).2 (Nat.prime_iff_prime_int.1 p.2)
      obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (Ideal.span {((p : ℕ) : ℤ)})
        (⊥ : Ideal (𝓞 K)) (by rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)
      have hQ0 : Q ≠ ⊥ := by
        intro h
        rw [h, Ideal.comap_bot_of_injective _ hinj] at hQc
        exact hp0 (Ideal.span_singleton_eq_bot.1 hQc.symm)
      exact ⟨⟨Q, hQ, hQ0⟩, hQc⟩
    choose f hf using key
    have hfinj : Function.Injective f := by
      intro p q hpq
      have h := hf p
      rw [hpq, hf q, Ideal.span_singleton_eq_span_singleton, Int.associated_iff_natAbs] at h
      exact Subtype.ext (by simpa using h.symm)
    haveI : Infinite {p : ℕ // p.Prime} := Nat.infinite_setOf_prime.to_subtype
    exact (Set.infinite_of_injective_forall_mem hfinj (fun p => (Finset.mem_coe.2 (hall (f p)))))
      (Finset.finite_toSet SK)

  have hcontU : ∀ χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ, (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)) → Continuous χ := by
    intro χ hχ
    refine Units.continuous_iff.mpr ⟨hχ, ?_⟩
    have : (fun z : (AdeleRing (𝓞 K) K)ˣ => (((χ z)⁻¹ : ℂˣ) : ℂ)) = fun z => ((χ z⁻¹ : ℂˣ) : ℂ) := by
      funext z; rw [map_inv]
    show Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => (((χ z)⁻¹ : ℂˣ) : ℂ)
    rw [this]
    exact hχ.comp continuous_inv
  have harch : ∀ χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ, (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)) →
      ∀ w : InfinitePlace K, ∃ u : ℂ, ∃ a : ℤ, LanglandsTunnell.Converse.IsArchCompAt K χ w u a := by
    intro χ hχ w
    rcases w.isReal_or_isComplex with hw | hw
    · obtain ⟨u, a, h⟩ := LanglandsTunnell.Converse.exists_isArchCompAt_of_isReal K χ (hcontU χ hχ) w hw
      exact ⟨u, _, h⟩
    · obtain ⟨u, k, h⟩ := LanglandsTunnell.Converse.exists_isArchCompAt_of_isComplex K χ (hcontU χ hχ) w hw
      exact ⟨u, k, h⟩
  choose uμ aμ hμA using (fun (e : ιE) (w : InfinitePlace K) => harch (μ e) (_hμcE e) w)
  choose uν aν hνA using (fun (e : ιE) (w : InfinitePlace K) => harch (ν e) (_hνcE e) w)

  obtain ⟨c34, R₀, A, h34⟩ := AutomorphicForm.forall_exists_setIntegral_norm_sq_lambdaT_axis_continuation_le_mul_mul_pow_of_isArchCompAt_of_ne_bot K N hNbot tysK hαm ιE μ ν _hμE _hνE _hμicE _hνicE _hμcE _hνcE
    nE φE _hφE _hφEK _hφEf _hφEjc _hφEhol _hφEKu _hφEflat _hφElev _hφEty _hφEon uμ uν aμ aν hμA hνA OE EE NE _hEE
    α β hα hαβ (AutomorphicForm.canonicalTruncationDomain K α β)

  have hCIJ := AutomorphicForm.continuous_and_integrable_and_memLp_two_integral_mul_conj_flat_section_of_matched_paleyWiener K α β hα hαβ ΦK cK uK d₁K d₂K TK hcK hd₁K hdK hcovK νZK ΩK hΩK SK ξK hξc hξt N hN tysK hξu hαm ι b cls hb hbn hbo hbs hbc ιE μ ν _hμE _hνE _hμicE _hνicE _hμcE _hνcE _hμν _hdistE nE φE _hφE _hφEK _hφEf _hφEjc _hφEhol _hφEKu _hφEflat _hφElev _hφEty _hφEon _hφEspan _hpairs OE EE NE _hEE ιP μP νP _hμP _hνP _hμicP _hνicP _hμcP _hμνP rP _hr _hdistP ψf _hψf _hψjc _hψhol _hψK _hψsm _hψKu _hνcP _hψdec ψ _hψ _hψrep em τ _hem _hψlev _hψty
  obtain ⟨-, -, -, hslab, hFD⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ
  have hfin : (adelicGLHaar (Fin 2) (𝓞 K) K) (AutomorphicForm.canonicalTruncationDomain K α β) < ⊤ := by
    have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain K α β hα hαβ
      (AutomorphicForm.canonicalTruncationDomain K α β) hFD
    rwa [Set.inter_eq_left.mpr hslab] at h
  haveI : IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) :=
    isFiniteMeasure_restrict.2 hfin.ne
  refine ⟨R₀, fun R hR => ?_⟩
  have hA : MemLp (fun x : AdelicGL2 (𝓞 K) K =>
      ∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)), (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
            ∂(maximalCompactHaar K)) *
        @AutomorphicForm.lambdaT _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)).nS _ _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)).ν
        (fun n => AutomorphicForm.unipotentGL2 n) (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
        (EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I)) x) 2
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := by

    have hper : ∀ i : ιP, MemLp (fun x : AdelicGL2 (𝓞 K) K => ∫ t : ℝ, ∑ j : Fin (nE (em i)), (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
                    ∂(maximalCompactHaar K)) *
        @AutomorphicForm.lambdaT _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
                  (fun M' => principalLevel (𝓞 K) K M' ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
                  (fun M' => principalLevel (𝓞 K) K M' ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                  (fun n => AutomorphicForm.unipotentGL2 n) (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                  (EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I)) x) 2
        ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := by
      intro i
      set Gi : ℝ × AdelicGL2 (𝓞 K) K → ℂ := fun p => ∑ j : Fin (nE (em i)), (∫ k, ψf i ((p.1 : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((p.1 + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
                    ∂(maximalCompactHaar K)) *
        @AutomorphicForm.lambdaT _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
                  (fun M' => principalLevel (𝓞 K) K M' ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
                  (fun M' => principalLevel (𝓞 K) K M' ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                  (fun n => AutomorphicForm.unipotentGL2 n) (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                  (EE (em i) j ((((p.1 + τ i : ℝ) : ℂ)) * Complex.I)) p.2 with hGi

      haveI : SecondCountableTopology (AdeleRing (𝓞 K) K) := NumberField.AdeleRing.secondCountableTopology K
      haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) := NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K

      set c : Fin (nE (em i)) → ℝ → ℂ := fun j t => (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
                    ∂(maximalCompactHaar K)) with hc
      have hcc : ∀ j, Continuous (c j) := fun j => (hCIJ i j).1

      have hEc : ∀ j, Continuous (fun p : ℝ × AdelicGL2 (𝓞 K) K => EE (em i) j ((((p.1 + τ i : ℝ) : ℂ)) * Complex.I) p.2) := by
        intro j
        have hax : ∀ t : ℝ, ((((t + τ i : ℝ) : ℂ)) * Complex.I) ∈ OE (em i) j := fun t => (_hEE (em i) j).2.2.1 (by simp)
        refine ((_hEE (em i) j).2.2.2.2.2.2.1).comp_continuous
          (f := fun p : ℝ × AdelicGL2 (𝓞 K) K => ((((p.1 + τ i : ℝ) : ℂ)) * Complex.I, p.2)) ?_ (fun p => ⟨hax p.1, Set.mem_univ _⟩)
        exact Continuous.prodMk ((Complex.continuous_ofReal.comp (continuous_fst.add continuous_const)).mul continuous_const) continuous_snd

      have hLmeas : ∀ j, Measurable (fun p : ℝ × AdelicGL2 (𝓞 K) K =>
          @AutomorphicForm.lambdaT _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
                  (fun M' => principalLevel (𝓞 K) K M' ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
                  (fun M' => principalLevel (𝓞 K) K M' ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                  (fun n => AutomorphicForm.unipotentGL2 n) (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                  (EE (em i) j ((((p.1 + τ i : ℝ) : ℂ)) * Complex.I)) p.2) := by
        intro j
        have hCT : Measurable (fun p : ℝ × AdelicGL2 (𝓞 K) K =>
            ∫ q, EE (em i) j ((((p.1 + τ i : ℝ) : ℂ)) * Complex.I) (AutomorphicForm.unipotentGL2 q * p.2)
              ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))) := by
          have hf : Continuous (fun pq : (ℝ × AdelicGL2 (𝓞 K) K) × AdeleRing (𝓞 K) K =>
              EE (em i) j ((((pq.1.1 + τ i : ℝ) : ℂ)) * Complex.I) (AutomorphicForm.unipotentGL2 pq.2 * pq.1.2)) :=
            (hEc j).comp (Continuous.prodMk (continuous_fst.comp continuous_fst)
              (((AutomorphicForm.continuous_unipotentGL2).comp continuous_snd).mul (continuous_snd.comp continuous_fst)))
          exact (hf.stronglyMeasurable.integral_prod_right'
            (ν := ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))).measurable
        have hHS : MeasurableSet ((fun p : ℝ × AdelicGL2 (𝓞 K) K => p.2) ⁻¹'
            AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)) :=
          measurable_snd ((isOpen_lt continuous_const (NumberField.AdelicHeight.continuous_adelicHeight K)).measurableSet)
        have hind : Measurable (fun p : ℝ × AdelicGL2 (𝓞 K) K =>
            Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
              (AutomorphicForm.constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
                (fun n => AutomorphicForm.unipotentGL2 n) (EE (em i) j ((((p.1 + τ i : ℝ) : ℂ)) * Complex.I))) p.2) := by
          have : (fun p : ℝ × AdelicGL2 (𝓞 K) K =>
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
                (AutomorphicForm.constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
                  (fun n => AutomorphicForm.unipotentGL2 n) (EE (em i) j ((((p.1 + τ i : ℝ) : ℂ)) * Complex.I))) p.2) =
              Set.indicator ((fun p : ℝ × AdelicGL2 (𝓞 K) K => p.2) ⁻¹'
                AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
                (fun p : ℝ × AdelicGL2 (𝓞 K) K => ∫ q, EE (em i) j ((((p.1 + τ i : ℝ) : ℂ)) * Complex.I) (AutomorphicForm.unipotentGL2 q * p.2)
                  ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))) := by
            funext p
            simp only [Set.indicator_apply, Set.mem_preimage, AutomorphicForm.constantTerm, AutomorphicForm.constantTermIntegrand]
          rw [this]
          exact hCT.indicator hHS
        exact (hEc j).measurable.sub hind
      have hGmeas : Measurable Gi := by
        refine Finset.measurable_sum _ fun j _ => ?_
        exact ((hcc j).measurable.comp measurable_fst).mul (hLmeas j)
      have hGm : AEStronglyMeasurable Gi ((volume : Measure ℝ).prod ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))) := hGmeas.aestronglyMeasurable

      have hKc : IsCompact ((adelicMaximalCompact K : Subgroup (AdelicGL2 (𝓞 K) K)) : Set (AdelicGL2 (𝓞 K) K)) := by
        have := isCompact_univ.image (continuous_subtype_val : Continuous (fun k : ↥(adelicMaximalCompact K) => (k : AdelicGL2 (𝓞 K) K)))
        rwa [Set.image_univ, Subtype.range_coe] at this
      obtain ⟨m, hm, ⟨B, hmB⟩, hmb⟩ := _hψdec i (A + 2) 0 _ hKc
      have hmb0 := hmb 0 (by simp)
      have hφc : ∀ (j' : Fin (nE (em i))) (s : ℂ), Continuous fun k : ↥(adelicMaximalCompact K) => φE (em i) j' s (k : AdelicGL2 (𝓞 K) K) :=
        fun j' s => ((_hφEjc (em i) j').comp (Continuous.prodMk continuous_const continuous_id)).comp continuous_subtype_val
      set I₀ : Fin (nE (em i)) → ℝ := fun j => ∫ k', ‖φE (em i) j 0 (k' : AdelicGL2 (𝓞 K) K)‖ ∂(maximalCompactHaar K) with hI₀
      have hI₀nn : ∀ j, 0 ≤ I₀ j := fun j => integral_nonneg fun _ => norm_nonneg _
      have hcb : ∀ (j : Fin (nE (em i))) (t : ℝ), (1 + |t|) ^ (A + 2) * ‖c j t‖ ≤ I₀ j * m t := by
        intro j t
        have hφint : Integrable (fun k' : ↥(adelicMaximalCompact K) => ‖φE (em i) j 0 (k' : AdelicGL2 (𝓞 K) K)‖) (maximalCompactHaar K) :=
          ((hφc j 0).norm).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
        have hpt : ∀ k' : ↥(adelicMaximalCompact K),
            (1 + |t|) ^ (A + 2) * ‖ψf i ((t : ℂ) * Complex.I) (k' : AdelicGL2 (𝓞 K) K) *
              conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k' : AdelicGL2 (𝓞 K) K))‖ ≤
            m t * ‖φE (em i) j 0 (k' : AdelicGL2 (𝓞 K) K)‖ := by
          intro k'
          rw [norm_mul, RCLike.norm_conj, _hφEflat (em i) j _ k', ← mul_assoc]
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          have := hmb0 t (k' : AdelicGL2 (𝓞 K) K) k'.2
          have e0 : (((0 : ℝ) : ℂ)) + ((t : ℝ) : ℂ) * Complex.I = (t : ℂ) * Complex.I := by push_cast; ring
          rwa [e0] at this
        have hint1 : Integrable (fun k' : ↥(adelicMaximalCompact K) => ψf i ((t : ℂ) * Complex.I) (k' : AdelicGL2 (𝓞 K) K) *
            conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k' : AdelicGL2 (𝓞 K) K))) (maximalCompactHaar K) :=
          ((((_hψjc i).comp (Continuous.prodMk continuous_const continuous_id)).comp continuous_subtype_val).mul
            (Complex.continuous_conj.comp (hφc j _))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
        calc (1 + |t|) ^ (A + 2) * ‖c j t‖ ≤ (1 + |t|) ^ (A + 2) * ∫ k', ‖ψf i ((t : ℂ) * Complex.I) (k' : AdelicGL2 (𝓞 K) K) *
              conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k' : AdelicGL2 (𝓞 K) K))‖ ∂(maximalCompactHaar K) := by
                rw [hc]; exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
          _ = ∫ k', (1 + |t|) ^ (A + 2) * ‖ψf i ((t : ℂ) * Complex.I) (k' : AdelicGL2 (𝓞 K) K) *
              conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k' : AdelicGL2 (𝓞 K) K))‖ ∂(maximalCompactHaar K) := (integral_const_mul _ _).symm
          _ ≤ ∫ k', m t * ‖φE (em i) j 0 (k' : AdelicGL2 (𝓞 K) K)‖ ∂(maximalCompactHaar K) :=
                integral_mono (hint1.norm.const_mul _) (hφint.const_mul _) hpt
          _ = I₀ j * m t := by rw [integral_const_mul, hI₀, mul_comm]
      have hmt : ∀ t, 0 ≤ m t := fun t => le_trans (by positivity) (hmb0 t (1 : AdelicGL2 (𝓞 K) K) (one_mem _))
      have hcB : ∀ (j : Fin (nE (em i))) (t : ℝ), ‖c j t‖ ≤ I₀ j * B := by
        intro j t
        have h1 : ‖c j t‖ ≤ (1 + |t|) ^ (A + 2) * ‖c j t‖ :=
          le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (by linarith [abs_nonneg t]))
        exact h1.trans ((hcb j t).trans (mul_le_mul_of_nonneg_left (hmB t) (hI₀nn j)))

      set W : ℝ → ℝ := fun t => 1 + ∑ w : InfinitePlace K, ‖2 * (t : ℂ) * Complex.I + (uμ (em i) w - uν (em i) w)‖ with hW
      have hW0 : ∀ t, 0 ≤ W t := fun t => by rw [hW]; positivity
      set D : ℝ := 1 + ∑ w : InfinitePlace K, (2 + 2 * |τ i| + ‖uμ (em i) w - uν (em i) w‖) with hD
      have hD1 : 1 ≤ D := by
        have h0 : 0 ≤ ∑ w : InfinitePlace K, (2 + 2 * |τ i| + ‖uμ (em i) w - uν (em i) w‖) :=
          Finset.sum_nonneg (fun w _ => by positivity)
        rw [hD]; linarith
      have hWle : ∀ t : ℝ, W (t + τ i) ≤ D * (1 + |t|) := by
        intro t
        rw [hW, hD, add_mul, one_mul, Finset.sum_mul]
        have ht : (0 : ℝ) ≤ |t| := abs_nonneg t
        refine add_le_add (by linarith) (Finset.sum_le_sum fun w _ => ?_)
        calc ‖2 * (((t + τ i : ℝ)) : ℂ) * Complex.I + (uμ (em i) w - uν (em i) w)‖
            ≤ ‖2 * (((t + τ i : ℝ)) : ℂ) * Complex.I‖ + ‖uμ (em i) w - uν (em i) w‖ := norm_add_le _ _
          _ = 2 * |t + τ i| + ‖uμ (em i) w - uν (em i) w‖ := by
              rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]; norm_num
          _ ≤ 2 * (|t| + |τ i|) + ‖uμ (em i) w - uν (em i) w‖ := by gcongr; exact abs_add_le _ _
          _ ≤ (2 + 2 * |τ i| + ‖uμ (em i) w - uν (em i) w‖) * (1 + |t|) := by
              nlinarith [abs_nonneg (τ i), norm_nonneg (uμ (em i) w - uν (em i) w)]
      have hWc : Continuous W := by
        rw [hW]
        refine continuous_const.add (continuous_finset_sum _ fun w _ => ?_)
        exact ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const |>.add continuous_const).norm

      set Mf : ℝ → ℝ := fun t => (nE (em i) : ℝ) * (∑ j : Fin (nE (em i)), ‖c j t‖ ^ 2) * (|c34| * (|R| + 1) * W (t + τ i) ^ A) with hMfdef
      have hM0 : ∀ t, 0 ≤ Mf t := by intro t; simp only [hMfdef]; positivity
      have hGt : ∀ t : ℝ, MemLp (fun x => Gi (t, x)) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ∧
          (∫ x, ‖Gi (t, x)‖ ^ 2 ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))) ≤ Mf t := by
        intro t
        have h34j := fun j : Fin (nE (em i)) => h34 (em i) j (t + τ i) R hR
        have hL2 : ∀ j : Fin (nE (em i)), MemLp (fun x : AdelicGL2 (𝓞 K) K =>
            @AutomorphicForm.lambdaT _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
                  (fun M' => principalLevel (𝓞 K) K M' ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
                  (fun M' => principalLevel (𝓞 K) K M' ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                  (fun n => AutomorphicForm.unipotentGL2 n) (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                  (EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I)) x) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := by
          intro j
          refine (memLp_two_iff_integrable_sq_norm ?_).2 (h34j j).1
          exact ((hLmeas j).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
        have hGi_eq : (fun x => Gi (t, x)) = fun x => ∑ j : Fin (nE (em i)), c j t *
            @AutomorphicForm.lambdaT _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
                  (fun M' => principalLevel (𝓞 K) K M' ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
                  (fun M' => principalLevel (𝓞 K) K M' ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                  (fun n => AutomorphicForm.unipotentGL2 n) (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                  (EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I)) x := by
          funext x; simp only [hGi, hc]
        have hGmem : MemLp (fun x => Gi (t, x)) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := by
          rw [hGi_eq]; exact memLp_finsetSum _ fun j _ => (hL2 j).const_mul (c j t)
        have hbound : ∀ j : Fin (nE (em i)), ∫ x, ‖@AutomorphicForm.lambdaT _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
                (fun M' => principalLevel (𝓞 K) K M' ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
                (fun M' => principalLevel (𝓞 K) K M' ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun n => AutomorphicForm.unipotentGL2 n) (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I)) x‖ ^ 2 ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ≤
            |c34| * (|R| + 1) * W (t + τ i) ^ A := by
          intro j
          refine (h34j j).2.trans ?_
          have : W (t + τ i) = 1 + ∑ w : InfinitePlace K, ‖2 * (((t + τ i : ℝ)) : ℂ) * Complex.I + (uμ (em i) w - uν (em i) w)‖ := by rw [hW]
          rw [← this]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self c34) (by positivity)) (pow_nonneg (hW0 _) _)
        have hint_L := fun j : Fin (nE (em i)) => (h34j j).1
        have hint_G := (memLp_two_iff_integrable_sq_norm hGmem.1).1 hGmem
        have hpt : ∀ x : AdelicGL2 (𝓞 K) K, ‖Gi (t, x)‖ ^ 2 ≤ (∑ j : Fin (nE (em i)), ‖c j t‖ ^ 2) *
            ∑ j : Fin (nE (em i)), ‖(fun x => Gi (t, x)) x‖ ^ 0 * ‖@AutomorphicForm.lambdaT _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
                  (fun M' => principalLevel (𝓞 K) K M' ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
                  (fun M' => principalLevel (𝓞 K) K M' ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                  (fun n => AutomorphicForm.unipotentGL2 n) (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                  (EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I)) x‖ ^ 2 := by
          intro x
          simp only [pow_zero, one_mul]
          have : Gi (t, x) = ∑ j : Fin (nE (em i)), c j t * @AutomorphicForm.lambdaT _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
                  (fun M' => principalLevel (𝓞 K) K M' ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
                  (fun M' => principalLevel (𝓞 K) K M' ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                  (fun n => AutomorphicForm.unipotentGL2 n) (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                  (EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I)) x := by
            simp only [hGi, hc]
          rw [this]
          exact Ws48.TPL.norm_sum_mul_sq_le _ _
        simp only [pow_zero, one_mul] at hpt
        refine ⟨hGmem, ?_⟩
        calc (∫ x, ‖Gi (t, x)‖ ^ 2 ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)))
            ≤ ∫ x, (∑ j : Fin (nE (em i)), ‖c j t‖ ^ 2) * ∑ j : Fin (nE (em i)), ‖@AutomorphicForm.lambdaT _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
                  (fun M' => principalLevel (𝓞 K) K M' ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
                  (fun M' => principalLevel (𝓞 K) K M' ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                  (fun n => AutomorphicForm.unipotentGL2 n) (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                  (EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I)) x‖ ^ 2
                ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) :=
              integral_mono hint_G ((integrable_finset_sum _ fun j _ => hint_L j).const_mul _) hpt
          _ = (∑ j : Fin (nE (em i)), ‖c j t‖ ^ 2) * ∑ j : Fin (nE (em i)), ∫ x, ‖@AutomorphicForm.lambdaT _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
                  (fun M' => principalLevel (𝓞 K) K M' ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
                  (fun M' => principalLevel (𝓞 K) K M' ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                  (fun n => AutomorphicForm.unipotentGL2 n) (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                  (EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I)) x‖ ^ 2
                ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := by
              rw [integral_const_mul, integral_finset_sum _ (fun j _ => hint_L j)]
          _ ≤ (∑ j : Fin (nE (em i)), ‖c j t‖ ^ 2) * ∑ j : Fin (nE (em i)), (|c34| * (|R| + 1) * W (t + τ i) ^ A) := by
              gcongr with j
              exact hbound j
          _ = Mf t := by
              simp only [hMfdef, Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
      have hMi : Integrable (fun t : ℝ => (1 + t ^ 2) * Mf t) := by
        have hB0 : 0 ≤ B := le_trans (hmt 0) (hmB 0)
        have hMc : Continuous Mf := by
          rw [hMfdef]
          refine (continuous_const.mul (continuous_finset_sum _ fun j _ => ((hcc j).norm.pow 2))).mul
            (continuous_const.mul ((hWc.comp (continuous_id.add continuous_const)).pow A))
        set Cst : ℝ := (nE (em i) : ℝ) * (|c34| * (|R| + 1) * D ^ A) * (B * ∑ j : Fin (nE (em i)), I₀ j ^ 2) with hCst
        refine Integrable.mono' (hm.const_mul Cst) (((continuous_const.add (continuous_id.pow 2)).mul hMc).aestronglyMeasurable)
          (Filter.Eventually.of_forall fun t => ?_)
        have hMt : 0 ≤ Mf t := hM0 t
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have e1 : (1 + t ^ 2) ≤ (1 + |t|) ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
        have e2 : W (t + τ i) ^ A ≤ D ^ A * (1 + |t|) ^ A := by
          rw [← mul_pow]; exact pow_le_pow_left₀ (hW0 _) (hWle t) A
        have e3 : ∀ j : Fin (nE (em i)), (1 + |t|) ^ (A + 2) * ‖c j t‖ ^ 2 ≤ I₀ j * m t * (I₀ j * B) := by
          intro j
          rw [sq, ← mul_assoc]
          exact mul_le_mul (hcb j t) (hcB j t) (norm_nonneg _) (mul_nonneg (hI₀nn j) (hmt t))
        have hS0 : 0 ≤ ∑ j : Fin (nE (em i)), ‖c j t‖ ^ 2 := Finset.sum_nonneg fun j _ => by positivity
        calc (1 + t ^ 2) * Mf t
            = (1 + t ^ 2) * ((nE (em i) : ℝ) * (∑ j : Fin (nE (em i)), ‖c j t‖ ^ 2) * (|c34| * (|R| + 1) * W (t + τ i) ^ A)) := by rw [hMfdef]
          _ ≤ (1 + |t|) ^ 2 * ((nE (em i) : ℝ) * (∑ j : Fin (nE (em i)), ‖c j t‖ ^ 2) * (|c34| * (|R| + 1) * (D ^ A * (1 + |t|) ^ A))) := by
              gcongr
          _ = ((nE (em i) : ℝ) * (|c34| * (|R| + 1) * D ^ A)) * ∑ j : Fin (nE (em i)), (1 + |t|) ^ (A + 2) * ‖c j t‖ ^ 2 := by
              rw [← Finset.mul_sum]; ring
          _ ≤ ((nE (em i) : ℝ) * (|c34| * (|R| + 1) * D ^ A)) * ∑ j : Fin (nE (em i)), I₀ j * m t * (I₀ j * B) :=
              mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => e3 j) (by positivity)
          _ = Cst * m t := by
              rw [hCst]
              have : ∑ j : Fin (nE (em i)), I₀ j * m t * (I₀ j * B) = (B * ∑ j : Fin (nE (em i)), I₀ j ^ 2) * m t := by
                rw [Finset.mul_sum, Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring
              rw [this]; ring
      exact (MeasureTheory.memLp_two_integral_and_integral_norm_sq_integral_le_of_integral_norm_sq_le_of_integrable_one_add_sq_mul _ Gi hGm Mf hM0 hGt hMi).1
    exact memLp_finsetSum Finset.univ (fun i _ => hper i)
  have hB := AutomorphicForm.lambdaT_sum_integral_sum_inner_mul_axis_continuation_eq_sum_integral_sum_inner_mul_lambdaT_of_mem_canonicalTruncationDomain_of_matched_paleyWiener K α β hα hαβ ΦK cK uK d₁K d₂K TK hcK hd₁K hdK hcovK νZK ΩK hΩK SK ξK hξc hξt N hN tysK hξu hαm ι b cls hb hbn hbo hbs hbc ιE μ ν _hμE _hνE _hμicE _hνicE _hμcE _hνcE _hμν _hdistE nE φE _hφE _hφEK _hφEf _hφEjc _hφEhol _hφEKu _hφEflat _hφElev _hφEty _hφEon _hφEspan _hpairs OE EE NE _hEE ιP μP νP _hμP _hνP _hμicP _hνicP _hμcP _hμνP rP _hr _hdistP ψf _hψf _hψjc _hψhol _hψK _hψsm _hψKu _hνcP _hψdec ψ _hψ _hψrep em τ _hem _hψlev _hψty R
  refine ⟨hA, hB, ?_⟩

  have haeΦ : ∀ᵐ g ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)),
      g ∈ AutomorphicForm.canonicalTruncationDomain K α β := by
    have hre : ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
          {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}).restrict
          (AutomorphicForm.canonicalTruncationDomain K α β) =
        (adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β) := by
      rw [Measure.restrict_restrict₀ hFD.nullMeasurableSet, Set.inter_eq_left.mpr hslab]
    rw [← hre]
    exact ae_restrict_mem₀ hFD.nullMeasurableSet
  refine hA.ae_eq ?_
  filter_upwards [haeΦ] with x hx
  exact (hB x hx).symm

end S_AutomorphicForm_exists_forall_memLp_two_lambdaT_sum_integral_sum_inner_mul_axis_continuation_restrict_canonicalTruncationDomain_of_matched_paleyWiener
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_memLp_two_lambdaT_sum_integral_sum_inner_mul_axis_continuation_restrict_canonicalTruncationDomain_of_matched_paleyWiener (solution)
