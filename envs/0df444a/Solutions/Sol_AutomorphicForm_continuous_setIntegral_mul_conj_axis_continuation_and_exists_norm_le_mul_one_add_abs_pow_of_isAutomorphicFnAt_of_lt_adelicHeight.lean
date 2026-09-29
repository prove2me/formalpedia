-- Prove2me | solution 1 for AutomorphicForm.continuous_setIntegral_mul_conj_axis_continuation_and_exists_norm_le_mul_one_add_abs_pow_of_isAutomorphicFnAt_of_lt_adelicHeight
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/dc0a1bf9-617d-557d-987e-506030344e92

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
import Theorems.Thm_AutomorphicForm_exists_isCompact_canonicalTruncationDomain_inter_setOf_adelicHeight_le_subset
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Theorems.Thm_AutomorphicForm_exists_forall_norm_axis_continuation_le_mul_pow_archParam_weight_of_isCompact_of_flat
import Theorems.Thm_NumberField_TateGlobal_exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_continuous_setIntegral_mul_conj_axis_continuation_and_exists_norm_le_mul_one_add_abs_pow_of_isAutomorphicFnAt_of_lt_adelicHeight
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite"
p2m_attr_erase "simp" "UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.CuspidalConstituent.rightRegular_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq"

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem Ws46.nullMeasurableSet_canonicalTruncationDomain (K : Type) [Field K] [NumberField K] (α β : ℝ) :
    NullMeasurableSet (AutomorphicForm.canonicalTruncationDomain K α β) (adelicGLHaar (Fin 2) (𝓞 K) K) := by
  classical
  by_cases h : ∃ d, AutomorphicForm.IsTruncationDatum K α β d
  · obtain ⟨-, -, -, hsub, hfd⟩ := AutomorphicForm.canonicalTruncationData_spec K h
    set S : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K) :=
      {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} with hS
    have hSm : MeasurableSet S := NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc K α β
    have h1 : NullMeasurableSet (AutomorphicForm.canonicalTruncationDomain K α β)
        ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict S) := hfd.nullMeasurableSet
    obtain ⟨t, -, htm, hts⟩ := h1.exists_measurable_superset_ae_eq
    have hsub' : AutomorphicForm.canonicalTruncationDomain K α β ⊆ S := hsub
    have hae : (t ∩ S : Set _) =ᵐ[adelicGLHaar (Fin 2) (𝓞 K) K] AutomorphicForm.canonicalTruncationDomain K α β := by
      have h2 := (ae_restrict_iff' hSm).1 (Filter.EventuallyEq.mem_iff hts)
      filter_upwards [h2] with x hx
      refine propext ⟨fun hxt => (hx hxt.2).1 hxt.1, fun hxs => ⟨(hx (hsub' hxs)).2 hxs, hsub' hxs⟩⟩
    exact (htm.inter hSm).nullMeasurableSet.congr hae
  · have : AutomorphicForm.canonicalTruncationDomain K α β = ∅ := by
      unfold AutomorphicForm.canonicalTruncationDomain AutomorphicForm.canonicalTruncationData
      rw [dif_neg h]
    rw [this]; exact nullMeasurableSet_empty

open AutomorphicForm in
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
      (u : AdelicGL2 (𝓞 K) K → ℂ)
      (_hu : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u)
      (_hub : ∃ T : ℝ, ∀ g ∈ AutomorphicForm.canonicalTruncationDomain K α β,
        T < NumberField.AdelicHeight.adelicHeight K g → u g = 0)
      (e : ιE) (j : Fin (nE e)),
    (Continuous fun t : ℝ => ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, u g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    ∃ (A : ℝ) (k : ℕ), ∀ t : ℝ, ‖∫ g in AutomorphicForm.canonicalTruncationDomain K α β, u g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)‖ ≤ A * (1 + |t|) ^ k  := by
  intro αm hαm ι b cls hb hbn hbo hbs hbc ιE _ μ ν _hμE _hνE _hμicE _hνicE _hμcE _hνcE _hμν _hdistE nE φE _hφE _hφEK _hφEf _hφEjc _hφEhol _hφEKu _hφEflat _hφElev _hφEty _hφEon _hφEspan _hpairs OE EE NE _hEE u _hu _hub e j
  letI := adeleBorel (𝓞 K) K
  haveI := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 K) K
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K

  obtain ⟨T, hT⟩ := _hub
  obtain ⟨Cset, hCc, hCsub⟩ :=
    AutomorphicForm.exists_isCompact_canonicalTruncationDomain_inter_setOf_adelicHeight_le_subset K α β hα hαβ T
  have hC0 : ∀ g ∈ AutomorphicForm.canonicalTruncationDomain K α β, g ∉ Cset → u g = 0 := by
    intro g hg hgC
    refine hT g hg (lt_of_not_ge fun hle => hgC (hCsub ⟨hg, hle⟩))
  have hmem : ∀ t : ℝ, ((t : ℂ) * Complex.I) ∈ OE e j := fun t => (_hEE e j).2.2.1 (by simp)
  have hEcont : ∀ t : ℝ, Continuous fun x : AdelicGL2 (𝓞 K) K => EE e j ((t : ℂ) * Complex.I) x := fun t =>
    ((_hEE e j).2.2.2.2.2.2.1).comp_continuous (Continuous.prodMk continuous_const continuous_id)
      (fun x => ⟨hmem t, Set.mem_univ _⟩)
  have hEcont_t : ∀ g : AdelicGL2 (𝓞 K) K, Continuous fun t : ℝ => EE e j ((t : ℂ) * Complex.I) g := fun g =>
    ((_hEE e j).2.2.2.2.1 g).continuousOn.comp_continuous (Complex.continuous_ofReal.mul continuous_const)
      (fun t => hmem t)

  obtain ⟨τμ, mμ, hτμ, hmμ, -⟩ :=
    NumberField.TateGlobal.exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar K (μ e) (_hμE e) (_hμcE e)
  obtain ⟨τν, mν, hτν, hmν, -⟩ :=
    NumberField.TateGlobal.exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar K (ν e) (_hνE e) (_hνcE e)
  have hξw : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm K z) ^ (0 : ℝ) : ℝ) := fun z => by
    rw [Real.rpow_zero]; exact hξu z
  obtain ⟨C₀, A, hC₀, hgrow⟩ :=
    AutomorphicForm.exists_forall_norm_axis_continuation_le_mul_pow_archParam_weight_of_isCompact_of_flat
      K SK ξK hξc hξt N hN tysK 0 hξw Cset hCc
  have hμν' : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ((μ e z : ℂˣ) : ℂ) * ((ν e z : ℂˣ) : ℂ) *
      (((NumberField.TateGlobal.ideleNorm K z) ^ (0 : ℝ) : ℝ) : ℂ) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) := by
    intro z
    rw [Real.rpow_zero, Complex.ofReal_one, mul_one, ← Units.val_mul, _hμν e z]
  have hφn : ∫ k, ‖φE e j 0 (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) ≤ 1 := by
    have h1 := _hφEon e j j
    rw [if_pos rfl] at h1
    have h2 : (∫ k, φE e j 0 (k : AdelicGL2 (𝓞 K) K) * conj (φE e j 0 (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) =
        ((∫ k, ‖φE e j 0 (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      beta_reduce
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [h2] at h1
    exact le_of_eq (by exact_mod_cast h1)
  have hE : ∀ (t : ℝ), ∀ y ∈ Cset, ‖EE e j ((t : ℂ) * Complex.I) y‖ ≤
      C₀ * (1 + ∑ v : InfinitePlace K, (|t + τμ v| + |t - τν v| + (|mμ v| : ℝ) + (|mν v| : ℝ))) ^ A :=
    fun t => hgrow hαm (μ e) (ν e) (_hμE e) (_hνE e) (_hμicE e) (_hνicE e) (_hμcE e) (_hνcE e) hμν' τμ τν hτμ hτν
      mμ mν hmμ hmν (φE e j) (_hφE e j) (_hφEK e j) (_hφEf e j) (_hφEjc e j) (_hφEhol e j) (_hφEKu e j)
      (_hφEflat e j) (_hφElev e j) (_hφEty e j) hφn (OE e j) (EE e j) (NE e j) (_hEE e j) t

  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = 1 + ∑ v : InfinitePlace K, (2 + |τμ v| + |τν v| + (|mμ v| : ℝ) + (|mν v| : ℝ)) := ⟨_, rfl⟩
  have hL1 : 1 ≤ L := by
    rw [hL]; refine le_add_of_nonneg_right (Finset.sum_nonneg fun v _ => by positivity)
  have hpoly : ∀ t : ℝ, 1 + ∑ v : InfinitePlace K, (|t + τμ v| + |t - τν v| + (|mμ v| : ℝ) + (|mν v| : ℝ)) ≤ L * (1 + |t|) := by
    intro t
    rw [hL, add_mul, one_mul, Finset.sum_mul]
    refine add_le_add (le_add_of_nonneg_right (abs_nonneg t)) (Finset.sum_le_sum fun v _ => ?_)
    have h1 : |t + τμ v| ≤ |t| + |τμ v| := abs_add_le _ _
    have h2 : |t - τν v| ≤ |t| + |τν v| := abs_sub _ _
    have h3 : (0 : ℝ) ≤ |((mμ v : ℤ) : ℝ)| := abs_nonneg _
    have h4 : (0 : ℝ) ≤ |((mν v : ℤ) : ℝ)| := abs_nonneg _
    nlinarith [abs_nonneg t, abs_nonneg (τμ v), abs_nonneg (τν v), h3, h4, mul_nonneg (abs_nonneg (τμ v)) (abs_nonneg t),
      mul_nonneg (abs_nonneg (τν v)) (abs_nonneg t), mul_nonneg h3 (abs_nonneg t), mul_nonneg h4 (abs_nonneg t)]
  have hE' : ∀ (t : ℝ), ∀ y ∈ Cset, ‖EE e j ((t : ℂ) * Complex.I) y‖ ≤ C₀ * L ^ A * (1 + |t|) ^ A := by
    intro t y hy
    refine (hE t y hy).trans ?_
    rw [mul_assoc, ← mul_pow]
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (hpoly t) A) hC₀.le

  set μ₀ := (adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β) with hμ₀
  have hu2 : MemLp u 2 μ₀ :=
    ((AutomorphicForm.lsXiMemberAt_iff (𝓞 K) K _ _ _ _ u).1 _hu).2
  have hCmeas : MeasurableSet Cset := hCc.measurableSet
  have hCfin : μ₀ Cset < ⊤ := (Measure.restrict_apply_le _ _).trans_lt hCc.measure_lt_top
  have hae : ∀ᵐ g ∂μ₀, g ∈ AutomorphicForm.canonicalTruncationDomain K α β := by
    rw [hμ₀]; exact ae_restrict_mem₀ (Ws46.nullMeasurableSet_canonicalTruncationDomain K α β)
  have huind : (Cset.indicator u) =ᵐ[μ₀] u := by
    filter_upwards [hae] with g hg
    by_cases hgC : g ∈ Cset
    · rw [Set.indicator_of_mem hgC]
    · rw [Set.indicator_of_notMem hgC, hC0 g hg hgC]
  have hu1 : Integrable u μ₀ := by
    have h2 : MemLp (Cset.indicator u) 2 μ₀ := hu2.indicator hCmeas
    have hsupp : ∀ x, x ∉ Cset → Cset.indicator u x = 0 := fun x hx => Set.indicator_of_notMem hx _
    have h1 : MemLp (Cset.indicator u) 1 μ₀ :=
      h2.mono_exponent_of_measure_support_ne_top hsupp hCfin.ne (by norm_num)
    exact (memLp_one_iff_integrable.1 h1).congr huind

  have hptw : ∀ (t : ℝ) (D : ℝ), C₀ * L ^ A * (1 + |t|) ^ A ≤ D → ∀ᵐ g ∂μ₀,
      ‖u g * conj (EE e j ((t : ℂ) * Complex.I) g)‖ ≤ ‖u g‖ * D := by
    intro t D hD
    filter_upwards [hae] with g hg
    by_cases hgC : g ∈ Cset
    · rw [norm_mul, RCLike.norm_conj]
      exact mul_le_mul_of_nonneg_left ((hE' t g hgC).trans hD) (norm_nonneg _)
    · rw [hC0 g hg hgC, zero_mul, norm_zero, zero_mul]
  have hmeasF : ∀ t : ℝ, AEStronglyMeasurable (fun g : AdelicGL2 (𝓞 K) K => u g * conj (EE e j ((t : ℂ) * Complex.I) g)) μ₀ :=
    fun t => hu1.aestronglyMeasurable.mul
      (Complex.continuous_conj.comp_aestronglyMeasurable (hEcont t).aestronglyMeasurable)
  have hIbound : ∀ t : ℝ, ‖∫ g in AutomorphicForm.canonicalTruncationDomain K α β, u g * conj (EE e j ((t : ℂ) * Complex.I) g)
      ∂(adelicGLHaar (Fin 2) (𝓞 K) K)‖ ≤ (∫ g, ‖u g‖ ∂μ₀) * (C₀ * L ^ A * (1 + |t|) ^ A) := by
    intro t
    rw [← hμ₀, ← integral_mul_const]
    exact norm_integral_le_of_norm_le (hu1.norm.mul_const _) (hptw t _ le_rfl)
  have hIcont : Continuous fun t : ℝ => ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
      u g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
    rw [← hμ₀]
    refine continuous_iff_continuousAt.2 fun t₀ => ?_
    refine continuousAt_of_dominated (bound := fun g => ‖u g‖ * (C₀ * L ^ A * (2 + |t₀|) ^ A))
      (Filter.Eventually.of_forall hmeasF) ?_ (hu1.norm.mul_const _) ?_
    · have hball : Set.Ioo (t₀ - 1) (t₀ + 1) ∈ 𝓝 t₀ := Ioo_mem_nhds (by linarith) (by linarith)
      filter_upwards [hball] with t ht
      refine hptw t _ ?_
      have : |t| ≤ 1 + |t₀| := by
        have := abs_sub_abs_le_abs_sub t t₀
        have : |t - t₀| ≤ 1 := abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩
        linarith
      refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) A) (by positivity)
    · exact Filter.Eventually.of_forall fun g =>
        (continuous_const.mul (Complex.continuous_conj.comp (hEcont_t g))).continuousAt
  refine ⟨hIcont, ⟨(∫ g, ‖u g‖ ∂μ₀) * (C₀ * L ^ A), A, fun t => ?_⟩⟩
  refine (hIbound t).trans ?_
  ring_nf
  rfl

end S_AutomorphicForm_continuous_setIntegral_mul_conj_axis_continuation_and_exists_norm_le_mul_one_add_abs_pow_of_isAutomorphicFnAt_of_lt_adelicHeight
end P2MW
export P2MW.S_AutomorphicForm_continuous_setIntegral_mul_conj_axis_continuation_and_exists_norm_le_mul_one_add_abs_pow_of_isAutomorphicFnAt_of_lt_adelicHeight (solution)
