-- Prove2me | solution 1 for AutomorphicForm.setIntegral_mul_conj_sum_integral_sum_inner_mul_axis_continuation_eq_sum_integral_sum_conj_inner_mul_setIntegral_of_isAutomorphicFnAt_of_lt_adelicHeight
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/f61e580c-5b99-516e-ab90-518c1645af42

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
import Theorems.Thm_AutomorphicForm_exists_forall_norm_axis_continuation_le_mul_pow_archParam_weight_of_isCompact_of_flat
import Theorems.Thm_NumberField_TateGlobal_exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar
import Theorems.Thm_AutomorphicForm_exists_isCompact_canonicalTruncationDomain_inter_setOf_adelicHeight_le_subset
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setIntegral_mul_conj_sum_integral_sum_inner_mul_axis_continuation_eq_sum_integral_sum_conj_inner_mul_setIntegral_of_isAutomorphicFnAt_of_lt_adelicHeight
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite"
p2m_attr_erase "simp" "UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.CuspidalConstituent.rightRegular_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq"

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace BenchLPacket

theorem mul_conj_integral_finset_sum {ι' : Type*} (s : Finset ι') (a : ℂ) (F : ι' → ℝ → ℂ)
    (h : ∀ j ∈ s, Integrable (fun t => a * conj (F j t))) :
    a * conj (∫ t, ∑ j ∈ s, F j t) = ∑ j ∈ s, ∫ t, a * conj (F j t) := by
  by_cases ha : a = 0
  · simp [ha]
  have hF : ∀ j ∈ s, Integrable (F j) := by
    intro j hj
    have h1 : Integrable (fun t => conj (F j t)) := by
      have := (h j hj).const_mul a⁻¹
      simpa only [← mul_assoc, inv_mul_cancel₀ ha, one_mul] using this
    exact (Complex.conjCLE.integrable_comp_iff).mp h1
  rw [integral_finsetSum s hF, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [← integral_conj, ← integral_const_mul]

end BenchLPacket

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
      (_hψty : ∀ i (s : ℂ), ψf i s ∈ archCutSubmodule K tysK)
      (u : AdelicGL2 (𝓞 K) K → ℂ)
      (_hu : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u)
      (_hub : ∃ T : ℝ, ∀ g ∈ AutomorphicForm.canonicalTruncationDomain K α β,
        T < NumberField.AdelicHeight.adelicHeight K g → u g = 0),
    (∀ (i : ιP) (j : Fin (nE (em i))), Integrable (fun t : ℝ =>
        conj (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
          (∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
              u g * conj (EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)))) ∧
    ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        u g * conj (∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)),
          (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
          EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)),
        conj (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
          (∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
              u g * conj (EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := by
  intro αm hαm ι b cls hb hbn hbo hbs hbc ιE _ μ ν _hμE _hνE _hμicE _hνicE _hμcE _hνcE _hμν _hdistE nE φE _hφE _hφEK _hφEf _hφEjc _hφEhol _hφEKu _hφEflat _hφElev _hφEty _hφEon _hφEspan _hpairs OE EE NE _hEE ιP _ μP νP _hμP _hνP _hμicP _hνicP _hμcP _hμνP rP _hr _hdistP ψf _hψf _hψjc _hψhol _hψK _hψsm _hψKu _hνcP _hψdec ψ _hψ _hψrep em τ _hem _hψlev _hψty u _hu _hub
  letI := adeleBorel (𝓞 K) K
  haveI := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 K) K
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K

  obtain ⟨cK, hcK⟩ : ∃ cK : ∀ i : ιP, Fin (nE (em i)) → ℝ → ℂ, ∀ i j t, cK i j t =
      ∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
        conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) :=
    ⟨_, fun _ _ _ => rfl⟩
  obtain ⟨EK, hEK⟩ : ∃ EK : ∀ i : ιP, Fin (nE (em i)) → ℝ → AdelicGL2 (𝓞 K) K → ℂ, ∀ i j t g, EK i j t g =
      EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g := ⟨_, fun _ _ _ _ => rfl⟩
  simp only [← hcK, ← hEK]
  set Φ₀ : Set (AdelicGL2 (𝓞 K) K) := AutomorphicForm.canonicalTruncationDomain K α β with hΦ₀
  set μG : Measure (AdelicGL2 (𝓞 K) K) := adelicGLHaar (Fin 2) (𝓞 K) K with hμG

  have huL2 : MemLp u 2 (μG.restrict Φ₀) :=
    ((AutomorphicForm.lsXiMemberAt_iff (𝓞 K) K (adelicGLHaar (Fin 2) (𝓞 K) K) ⊤ ξK
      (AutomorphicForm.canonicalTruncationDomain K α β) u).mp _hu).2
  have huae : AEStronglyMeasurable u (μG.restrict Φ₀) := huL2.1
  have husq : Integrable (fun g => ‖u g‖ ^ 2) (μG.restrict Φ₀) :=
    (memLp_two_iff_integrable_sq_norm huae).mp huL2
  have hΦae : ∀ᵐ g ∂(μG.restrict Φ₀), g ∈ Φ₀ := by
    obtain ⟨-, -, -, hsub, hFD⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ
    rw [← Measure.restrict_restrict_of_subset hsub]
    exact ae_restrict_mem₀ hFD.nullMeasurableSet
  obtain ⟨T, hT⟩ := _hub
  obtain ⟨C, hCc, hCsub⟩ :=
    AutomorphicForm.exists_isCompact_canonicalTruncationDomain_inter_setOf_adelicHeight_le_subset K α β hα hαβ T
  have huC : ∀ g ∈ Φ₀, u g ≠ 0 → g ∈ C :=
    fun g hg hu0 => hCsub ⟨hg, le_of_not_gt fun h => hu0 (hT g hg h)⟩
  have hCmeas : MeasurableSet C := hCc.measurableSet
  have hCfin : μG C < ⊤ := hCc.measure_lt_top
  have hind : Integrable (C.indicator fun _ : AdelicGL2 (𝓞 K) K => (1 : ℝ)) (μG.restrict Φ₀) := by
    refine (integrable_indicator_iff hCmeas).2 ?_
    exact integrableOn_const ((Measure.restrict_apply_le _ _).trans_lt hCfin).ne
  have hFint : Integrable (fun g => ‖u g‖ ^ 2 + C.indicator (fun _ : AdelicGL2 (𝓞 K) K => (1 : ℝ)) g)
      (μG.restrict Φ₀) := husq.add hind

  have hmemO : ∀ (e : ιE) (j : Fin (nE e)) (t : ℝ), ((t : ℂ) * Complex.I) ∈ OE e j :=
    fun e j t => (_hEE e j).2.2.1 (by simp)
  have hEKjc : ∀ (i : ιP) (j : Fin (nE (em i))),
      Continuous fun p : ℝ × AdelicGL2 (𝓞 K) K => EK i j p.1 p.2 := by
    intro i j
    have : (fun p : ℝ × AdelicGL2 (𝓞 K) K => EK i j p.1 p.2) =
        (fun p : ℂ × AdelicGL2 (𝓞 K) K => EE (em i) j p.1 p.2) ∘
          (fun p : ℝ × AdelicGL2 (𝓞 K) K => ((((p.1 + τ i : ℝ) : ℂ)) * Complex.I, p.2)) := by
      funext p; simp only [Function.comp, hEK]
    rw [this]
    refine ((_hEE (em i) j).2.2.2.2.2.2.1).comp_continuous ?_ ?_
    · exact ((Complex.continuous_ofReal.comp (continuous_fst.add continuous_const)).mul
        continuous_const).prodMk continuous_snd
    · intro p; exact ⟨hmemO (em i) j _, Set.mem_univ _⟩
  have hKc : IsCompact ((adelicMaximalCompact K : Subgroup (AdelicGL2 (𝓞 K) K)) :
      Set (AdelicGL2 (𝓞 K) K)) := AutomorphicForm.isCompact_adelicMaximalCompact K

  have claim : ∀ (i : ιP) (j : Fin (nE (em i))),
      Integrable (fun p : AdelicGL2 (𝓞 K) K × ℝ => u p.1 * conj (cK i j p.2 * EK i j p.2 p.1))
        ((μG.restrict Φ₀).prod volume) := by
    intro i j

    obtain ⟨τμ, mμ, hτμ, hmμ, -⟩ :=
      NumberField.TateGlobal.exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar K (μ (em i)) (_hμE (em i))
        (_hμcE (em i))
    obtain ⟨τν, mν, hτν, hmν, -⟩ :=
      NumberField.TateGlobal.exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar K (ν (em i)) (_hνE (em i))
        (_hνcE (em i))
    have hξw : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm K z) ^ (0 : ℝ) : ℝ) :=
      fun z => by rw [Real.rpow_zero]; exact hξu z
    obtain ⟨C₀, A, hC₀, hgrow⟩ :=
      AutomorphicForm.exists_forall_norm_axis_continuation_le_mul_pow_archParam_weight_of_isCompact_of_flat
        K SK ξK hξc hξt N hN tysK 0 hξw C hCc
    have hμν' : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ((μ (em i) z : ℂˣ) : ℂ) * ((ν (em i) z : ℂˣ) : ℂ) *
        (((NumberField.TateGlobal.ideleNorm K z) ^ (0 : ℝ) : ℝ) : ℂ) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) := by
      intro z
      rw [Real.rpow_zero, Complex.ofReal_one, mul_one, ← Units.val_mul, _hμν (em i) z]
    have hφn : ∫ k, ‖φE (em i) j 0 (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) ≤ 1 := by
      have h1 := _hφEon (em i) j j
      rw [if_pos rfl] at h1
      have h2 : (∫ k, φE (em i) j 0 (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j 0 (k : AdelicGL2 (𝓞 K) K))
          ∂(maximalCompactHaar K)) =
          ((∫ k, ‖φE (em i) j 0 (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) : ℝ) : ℂ) := by
        rw [← integral_complex_ofReal]
        refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
        beta_reduce
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [h2] at h1
      exact le_of_eq (by exact_mod_cast h1)
    have hE : ∀ (t : ℝ), ∀ y ∈ C, ‖EE (em i) j ((t : ℂ) * Complex.I) y‖ ≤
        C₀ * (1 + ∑ v : InfinitePlace K, (|t + τμ v| + |t - τν v| + (|mμ v| : ℝ) + (|mν v| : ℝ))) ^ A :=
      fun t => hgrow hαm (μ (em i)) (ν (em i)) (_hμE (em i)) (_hνE (em i)) (_hμicE (em i)) (_hνicE (em i))
        (_hμcE (em i)) (_hνcE (em i)) hμν' τμ τν hτμ hτν mμ mν hmμ hmν (φE (em i) j) (_hφE (em i) j)
        (_hφEK (em i) j) (_hφEf (em i) j) (_hφEjc (em i) j) (_hφEhol (em i) j) (_hφEKu (em i) j)
        (_hφEflat (em i) j) (_hφElev (em i) j) (_hφEty (em i) j) hφn (OE (em i) j) (EE (em i) j)
        (NE (em i) j) (_hEE (em i) j) t
    obtain ⟨L, hL⟩ : ∃ L : ℝ, L = 1 + ∑ v : InfinitePlace K,
        (2 + |τμ v| + |τν v| + (|mμ v| : ℝ) + (|mν v| : ℝ)) := ⟨_, rfl⟩
    have hL1 : 1 ≤ L := by
      rw [hL]; refine le_add_of_nonneg_right (Finset.sum_nonneg fun v _ => by positivity)
    have hL0 : 0 ≤ L := zero_le_one.trans hL1
    have hpoly : ∀ t : ℝ, 1 + ∑ v : InfinitePlace K, (|t + τμ v| + |t - τν v| + (|mμ v| : ℝ) + (|mν v| : ℝ)) ≤
        L * (1 + |t|) := by
      intro t
      rw [hL, add_mul, one_mul, Finset.sum_mul]
      refine add_le_add (le_add_of_nonneg_right (abs_nonneg t)) (Finset.sum_le_sum fun v _ => ?_)
      have h1 : |t + τμ v| ≤ |t| + |τμ v| := abs_add_le _ _
      have h2 : |t - τν v| ≤ |t| + |τν v| := abs_sub _ _
      have h3 : (0 : ℝ) ≤ |((mμ v : ℤ) : ℝ)| := abs_nonneg _
      have h4 : (0 : ℝ) ≤ |((mν v : ℤ) : ℝ)| := abs_nonneg _
      nlinarith [abs_nonneg t, abs_nonneg (τμ v), abs_nonneg (τν v), h3, h4,
        mul_nonneg (abs_nonneg (τμ v)) (abs_nonneg t), mul_nonneg (abs_nonneg (τν v)) (abs_nonneg t),
        mul_nonneg h3 (abs_nonneg t), mul_nonneg h4 (abs_nonneg t)]
    have hE' : ∀ (t : ℝ), ∀ y ∈ C, ‖EE (em i) j ((t : ℂ) * Complex.I) y‖ ≤ C₀ * L ^ A * (1 + |t|) ^ A := by
      intro t y hy
      refine (hE t y hy).trans ?_
      rw [mul_assoc, ← mul_pow]
      refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (hpoly t) A) hC₀.le

    set M₁ : ℝ := C₀ * L ^ A * (1 + |τ i|) ^ A with hM₁
    have hM₁0 : 0 ≤ M₁ := by
      rw [hM₁]; exact mul_nonneg (mul_nonneg hC₀.le (pow_nonneg hL0 _)) (pow_nonneg (by positivity) _)
    have hEsh : ∀ (t : ℝ), ∀ y ∈ C, ‖EK i j t y‖ ≤ M₁ * (1 + |t|) ^ A := by
      intro t y hy
      rw [hEK, hM₁]
      refine (hE' (t + τ i) y hy).trans ?_
      have h1 : 1 + |t + τ i| ≤ (1 + |τ i|) * (1 + |t|) := by
        nlinarith [abs_add_le t (τ i), abs_nonneg t, abs_nonneg (τ i), mul_nonneg (abs_nonneg (τ i)) (abs_nonneg t)]
      calc C₀ * L ^ A * (1 + |t + τ i|) ^ A ≤ C₀ * L ^ A * ((1 + |τ i|) * (1 + |t|)) ^ A :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1 A)
              (mul_nonneg hC₀.le (pow_nonneg hL0 _))
        _ = C₀ * L ^ A * (1 + |τ i|) ^ A * (1 + |t|) ^ A := by rw [mul_pow]; ring

    obtain ⟨m, hm_int, ⟨B, hmB⟩, hdec⟩ := _hψdec i A 0 _ hKc
    have hdec' : ∀ (t : ℝ) (k : adelicMaximalCompact K),
        (1 + |t|) ^ A * ‖ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖ ≤ m t := by
      intro t k
      have := hdec 0 (by simp) t k k.2
      simpa only [Complex.ofReal_zero, zero_add] using this
    have hm0 : ∀ t, 0 ≤ m t := fun t =>
      le_trans (mul_nonneg (pow_nonneg (by positivity) _) (norm_nonneg _)) (hdec' t 1)
    have hB0 : 0 ≤ B := (hm0 0).trans (hmB 0)
    have hψB : ∀ (t : ℝ) (k : adelicMaximalCompact K), ‖ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖ ≤ B := by
      intro t k
      have h1 : (1 : ℝ) ≤ (1 + |t|) ^ A := one_le_pow₀ (by linarith [abs_nonneg t])
      have h2 := hdec' t k
      have h3 : ‖ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖ ≤
          (1 + |t|) ^ A * ‖ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖ :=
        le_mul_of_one_le_left (norm_nonneg _) h1
      exact h3.trans (h2.trans (hmB t))
    have hψm : ∀ (t : ℝ) (k : adelicMaximalCompact K),
        ‖ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖ ≤ m t / (1 + |t|) ^ A := by
      intro t k
      rw [le_div_iff₀ (by positivity), mul_comm]
      exact hdec' t k
    have hφc0 : Continuous fun k : adelicMaximalCompact K => φE (em i) j 0 (k : AdelicGL2 (𝓞 K) K) :=
      (_hφEjc (em i) j).comp (continuous_const.prodMk continuous_subtype_val)
    obtain ⟨Bφ, hBφ⟩ : ∃ Bφ : ℝ, ∀ k : adelicMaximalCompact K, ‖φE (em i) j 0 (k : AdelicGL2 (𝓞 K) K)‖ ≤ Bφ := by
      obtain ⟨Bφ, h⟩ := (isCompact_univ (X := adelicMaximalCompact K)).exists_bound_of_continuousOn
        hφc0.continuousOn
      exact ⟨Bφ, fun k => h k (Set.mem_univ _)⟩
    have hBφ0 : 0 ≤ Bφ := (norm_nonneg _).trans (hBφ 1)

    have hcKint : ∀ t : ℝ, Continuous fun k : adelicMaximalCompact K =>
        ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
          conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) := by
      intro t
      exact ((_hψjc i).comp (continuous_const.prodMk continuous_subtype_val)).mul
        (Complex.continuous_conj.comp ((_hφEjc (em i) j).comp (continuous_const.prodMk continuous_subtype_val)))
    have hcKcont : Continuous (cK i j) := by
      have hfun : cK i j = fun t : ℝ => ∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
          conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) :=
        funext (hcK i j)
      rw [hfun]
      refine continuous_of_dominated (bound := fun _ => B * Bφ) ?_ ?_ (integrable_const _) ?_
      · intro t; exact (hcKint t).aestronglyMeasurable
      · intro t
        refine Filter.Eventually.of_forall fun k => ?_
        rw [norm_mul, RCLike.norm_conj, _hφEflat (em i) j]
        exact mul_le_mul (hψB t k) (hBφ k) (norm_nonneg _) hB0
      · refine Filter.Eventually.of_forall fun k => ?_
        exact (((_hψjc i).comp ((Complex.continuous_ofReal.mul continuous_const).prodMk continuous_const)).mul
          (Complex.continuous_conj.comp ((_hφEjc (em i) j).comp
            (((Complex.continuous_ofReal.comp (continuous_id.add continuous_const)).mul continuous_const).prodMk
              continuous_const))))
    have hcKb : ∀ t : ℝ, ‖cK i j t‖ ≤ m t / (1 + |t|) ^ A * Bφ := by
      intro t
      rw [hcK]
      have := norm_integral_le_of_norm_le_const (μ := maximalCompactHaar K) (C := m t / (1 + |t|) ^ A * Bφ)
        (f := fun k : adelicMaximalCompact K => ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
          conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)))
        (Filter.Eventually.of_forall fun k => by
          rw [norm_mul, RCLike.norm_conj, _hφEflat (em i) j]
          exact mul_le_mul (hψm t k) (hBφ k) (norm_nonneg _) (div_nonneg (hm0 t) (by positivity)))
      simpa only [measure_univ, ENNReal.toReal_one, mul_one, probReal_univ] using this

    set Mc : ℝ := Bφ * M₁ with hMc
    have hMc0 : 0 ≤ Mc := mul_nonneg hBφ0 hM₁0
    have hbound_int : Integrable (fun p : AdelicGL2 (𝓞 K) K × ℝ =>
        (‖u p.1‖ ^ 2 + C.indicator (fun _ : AdelicGL2 (𝓞 K) K => (1 : ℝ)) p.1) * (Mc * m p.2))
        ((μG.restrict Φ₀).prod volume) :=
      hFint.mul_prod (hm_int.const_mul Mc)
    have hGmeas : AEStronglyMeasurable
        (fun p : AdelicGL2 (𝓞 K) K × ℝ => u p.1 * conj (cK i j p.2 * EK i j p.2 p.1))
        ((μG.restrict Φ₀).prod volume) := by
      have h1 : AEStronglyMeasurable (fun p : AdelicGL2 (𝓞 K) K × ℝ => u p.1) ((μG.restrict Φ₀).prod volume) :=
        huae.comp_fst
      have h2 : Continuous (fun p : AdelicGL2 (𝓞 K) K × ℝ => conj (cK i j p.2 * EK i j p.2 p.1)) :=
        Complex.continuous_conj.comp ((hcKcont.comp continuous_snd).mul
          ((hEKjc i j).comp (continuous_snd.prodMk continuous_fst)))
      exact h1.mul h2.aestronglyMeasurable
    have hΦae' : ∀ᵐ p ∂((μG.restrict Φ₀).prod (volume : Measure ℝ)), p.1 ∈ Φ₀ :=
      (Measure.quasiMeasurePreserving_fst (μ := μG.restrict Φ₀) (ν := (volume : Measure ℝ))).ae hΦae
    refine hbound_int.mono' hGmeas ?_
    filter_upwards [hΦae'] with p hp
    by_cases hu0 : u p.1 = 0
    · rw [hu0, zero_mul, norm_zero]
      exact mul_nonneg (add_nonneg (by positivity) (Set.indicator_nonneg (fun _ _ => zero_le_one) _))
        (mul_nonneg hMc0 (hm0 _))
    have hpC : p.1 ∈ C := huC p.1 hp hu0
    have h1 := hcKb p.2
    have h2 := hEsh p.2 p.1 hpC
    have h3 : ‖u p.1‖ ≤ ‖u p.1‖ ^ 2 + 1 := by nlinarith [sq_nonneg (‖u p.1‖ - 1), norm_nonneg (u p.1)]
    have hpos : (1 + |p.2|) ^ A ≠ 0 := by positivity
    have h4 : (m p.2 / (1 + |p.2|) ^ A * Bφ) * (M₁ * (1 + |p.2|) ^ A) = Mc * m p.2 := by
      rw [hMc]; field_simp
    calc ‖u p.1 * conj (cK i j p.2 * EK i j p.2 p.1)‖ = ‖u p.1‖ * (‖cK i j p.2‖ * ‖EK i j p.2 p.1‖) := by
          rw [norm_mul, RCLike.norm_conj, norm_mul]
      _ ≤ (‖u p.1‖ ^ 2 + 1) * ((m p.2 / (1 + |p.2|) ^ A * Bφ) * (M₁ * (1 + |p.2|) ^ A)) :=
          mul_le_mul h3 (mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg (div_nonneg (hm0 _) (by positivity)) hBφ0))
            (by positivity) (by positivity)
      _ = (‖u p.1‖ ^ 2 + C.indicator (fun _ : AdelicGL2 (𝓞 K) K => (1 : ℝ)) p.1) * (Mc * m p.2) := by
          rw [Set.indicator_of_mem hpC, h4]

  have hinner : ∀ (i : ιP) (j : Fin (nE (em i))) (t : ℝ),
      ∫ g in Φ₀, u g * conj (cK i j t * EK i j t g) ∂μG = conj (cK i j t) * ∫ g in Φ₀, u g * conj (EK i j t g) ∂μG := by
    intro i j t
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    beta_reduce
    rw [map_mul]; ring
  have hΘ : ∀ (i : ιP) (j : Fin (nE (em i))),
      Integrable (fun t : ℝ => conj (cK i j t) * ∫ g in Φ₀, u g * conj (EK i j t g) ∂μG) := by
    intro i j
    have := (claim i j).integral_prod_right
    refine this.congr (Filter.Eventually.of_forall fun t => ?_)
    exact hinner i j t
  refine ⟨hΘ, ?_⟩
  have hpt : ∀ᵐ g ∂(μG.restrict Φ₀),
      u g * conj (∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)), cK i j t * EK i j t g) =
        ∑ i : ιP, ∑ j : Fin (nE (em i)), ∫ t : ℝ, u g * conj (cK i j t * EK i j t g) := by
    have hae : ∀ᵐ g ∂(μG.restrict Φ₀), ∀ (i : ιP) (j : Fin (nE (em i))),
        Integrable (fun t : ℝ => u g * conj (cK i j t * EK i j t g)) := by
      refine ae_all_iff.2 fun i => ae_all_iff.2 fun j => ?_
      exact (claim i j).prod_right_ae
    filter_upwards [hae] with g hg
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact BenchLPacket.mul_conj_integral_finset_sum Finset.univ (u g) (fun j t => cK i j t * EK i j t g)
      (fun j _ => hg i j)
  rw [integral_congr_ae hpt]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => (claim i j).integral_prod_left)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => (claim i j).integral_prod_left)]
  rw [integral_finsetSum _ (fun j _ => hΘ i j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_integral_swap (claim i j)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  exact hinner i j t

end S_AutomorphicForm_setIntegral_mul_conj_sum_integral_sum_inner_mul_axis_continuation_eq_sum_integral_sum_conj_inner_mul_setIntegral_of_isAutomorphicFnAt_of_lt_adelicHeight
end P2MW
export P2MW.S_AutomorphicForm_setIntegral_mul_conj_sum_integral_sum_inner_mul_axis_continuation_eq_sum_integral_sum_conj_inner_mul_setIntegral_of_isAutomorphicFnAt_of_lt_adelicHeight (solution)
