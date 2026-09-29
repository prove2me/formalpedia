-- Prove2me | solution 1 for AutomorphicForm.exists_forall_memLp_two_indicator_highSet_sum_integral_sum_inner_mul_add_inv_vol_mul_axis_continuation_weylIntertwining_of_matched_paleyWiener
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/021992bd-b9d6-56f7-9cf8-bf354c0fa676

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
import Theorems.Thm_AutomorphicForm_exists_forall_norm_axis_continuation_weylIntertwiningIntegral_le_mul_pow_of_flat
import Theorems.Thm_AutomorphicForm_flat_section_centralScalar_mul_diagOne_mul_eq_mul_ideleNorm_cpow_and_inv_vol_mul_axis_continuation_weylIntertwining_eq_and_rationalTorusUnipotent_mul_of_matched_paleyWiener
import Theorems.Thm_AutomorphicForm_lintegral_maximalCompact_lintegral_Ioi_enorm_sq_integral_sum_inner_mul_cpow_mul_flat_section_add_inv_vol_mul_axis_continuation_weylIntertwining_mul_inv_lt_top_of_matched_paleyWiener
import Theorems.Thm_AutomorphicForm_exists_forall_setLIntegral_canonicalTruncationDomain_inter_lt_adelicHeight_le_mul_lintegral_Ioi_of_le_ideleNorm_mul
import Theorems.Thm_AutomorphicForm_continuous_and_integrable_and_memLp_two_integral_mul_conj_flat_section_of_matched_paleyWiener
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_memLp_two_indicator_highSet_sum_integral_sum_inner_mul_add_inv_vol_mul_axis_continuation_weylIntertwining_of_matched_paleyWiener
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg"
p2m_attr_erase "simp" "RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

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
      (_hψty : ∀ i (s : ℂ), ψf i s ∈ archCutSubmodule K tysK)
,
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      MemLp
        (fun g : AdelicGL2 (𝓞 K) K =>
          (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)).indicator
            (fun g : AdelicGL2 (𝓞 K) K => ∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)),
              (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
                  ∂(maximalCompactHaar K)) *
                (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g +
                  ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g))
            g)
        2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := by
  intro αm hαm ι b cls hb hbn hbo hbs hbc ιE _iC μ ν _hμE _hνE _hμicE _hνicE _hμcE _hνcE _hμν _hdistE nE φE _hφE _hφEK _hφEf _hφEjc _hφEhol _hφEKu _hφEflat _hφElev _hφEty _hφEon _hφEspan _hpairs OE EE NE _hEE ιP _iP μP νP _hμP _hνP _hμicP _hνicP _hμcP _hμνP rP _hr _hdistP ψf _hψf _hψjc _hψhol _hψK _hψsm _hψKu _hνcP _hψdec ψ _hψ _hψrep em τ _hem _hψlev _hψty
  classical
  letI hMSA : MeasurableSpace (AdeleRing (𝓞 K) K) := NumberField.AdelicHaar.adeleBorel (𝓞 K) K
  haveI := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 K) K
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K) := NumberField.AdeleRing.secondCountableTopology K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) := NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K

  have hC1 := AutomorphicForm.flat_section_centralScalar_mul_diagOne_mul_eq_mul_ideleNorm_cpow_and_inv_vol_mul_axis_continuation_weylIntertwining_eq_and_rationalTorusUnipotent_mul_of_matched_paleyWiener K α β hα hαβ ΦK cK uK d₁K d₂K TK hcK hd₁K hdK hcovK νZK ΩK hΩK SK ξK hξc hξt N hN tysK hξu hαm ι b cls hb hbn hbo hbs hbc ιE μ ν _hμE _hνE _hμicE _hνicE _hμcE _hνcE _hμν _hdistE nE φE _hφE _hφEK _hφEf _hφEjc _hφEhol _hφEKu _hφEflat _hφElev _hφEty _hφEon _hφEspan _hpairs OE EE NE _hEE ιP μP νP _hμP _hνP _hμicP _hνicP _hμcP _hμνP rP _hr _hdistP ψf _hψf _hψjc _hψhol _hψK _hψsm _hψKu _hνcP _hψdec ψ _hψ _hψrep em τ _hem _hψlev _hψty
  have hC2 := AutomorphicForm.lintegral_maximalCompact_lintegral_Ioi_enorm_sq_integral_sum_inner_mul_cpow_mul_flat_section_add_inv_vol_mul_axis_continuation_weylIntertwining_mul_inv_lt_top_of_matched_paleyWiener K α β hα hαβ ΦK cK uK d₁K d₂K TK hcK hd₁K hdK hcovK νZK ΩK hΩK SK ξK hξc hξt N hN tysK hξu hαm ι b cls hb hbn hbo hbs hbc ιE μ ν _hμE _hνE _hμicE _hνicE _hμcE _hνcE _hμν _hdistE nE φE _hφE _hφEK _hφEf _hφEjc _hφEhol _hφEKu _hφEflat _hφElev _hφEty _hφEon _hφEspan _hpairs OE EE NE _hEE ιP μP νP _hμP _hνP _hμicP _hνicP _hμcP _hμνP rP _hr _hdistP ψf _hψf _hψjc _hψhol _hψK _hψsm _hψKu _hνcP _hψdec ψ _hψ _hψrep em τ _hem _hψlev _hψty
  obtain ⟨C3c, hC3ne, hC3⟩ := AutomorphicForm.exists_forall_setLIntegral_canonicalTruncationDomain_inter_lt_adelicHeight_le_mul_lintegral_Ioi_of_le_ideleNorm_mul K α β hα hαβ
  have hCIJ := AutomorphicForm.continuous_and_integrable_and_memLp_two_integral_mul_conj_flat_section_of_matched_paleyWiener K α β hα hαβ ΦK cK uK d₁K d₂K TK hcK hd₁K hdK hcovK νZK ΩK hΩK SK ξK hξc hξt N hN tysK hξu hαm ι b cls hb hbn hbo hbs hbc ιE μ ν _hμE _hνE _hμicE _hνicE _hμcE _hνcE _hμν _hdistE nE φE _hφE _hφEK _hφEf _hφEjc _hφEhol _hφEKu _hφEflat _hφElev _hφEty _hφEon _hφEspan _hpairs OE EE NE _hEE ιP μP νP _hμP _hνP _hμicP _hνicP _hμcP _hμνP rP _hr _hdistP ψf _hψf _hψjc _hψhol _hψK _hψsm _hψKu _hνcP _hψdec ψ _hψ _hψrep em τ _hem _hψlev _hψty
  refine ⟨0, fun R _ => ?_⟩

  set c : (i : ιP) → Fin (nE (em i)) → ℝ → ℂ := fun i j t => (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
                  ∂(maximalCompactHaar K)) with hc
  set EX : AdelicGL2 (𝓞 K) K → ℂ := fun g => ∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)),
      (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
                  ∂(maximalCompactHaar K)) *
        (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g + ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g) with hEX
  set Aamp : ιP → ℝ → ↥(adelicMaximalCompact K) → ℂ := fun i y k => ∫ t : ℝ, ∑ j : Fin (nE (em i)),
      (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
                  ∂(maximalCompactHaar K)) * (((y : ℝ) : ℂ) ^ ((((t + τ i : ℝ) : ℂ)) * Complex.I) * φE (em i) j 0 (k : AdelicGL2 (𝓞 K) K)) with hA
  set Bamp : ιP → ℝ → ↥(adelicMaximalCompact K) → ℂ := fun i y k => ∫ t : ℝ, ∑ j : Fin (nE (em i)),
      (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
                  ∂(maximalCompactHaar K)) * (((y : ℝ) : ℂ) ^ (-((((t + τ i : ℝ) : ℂ)) * Complex.I)) * (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))) with hB
  set G : ℝ → ↥(adelicMaximalCompact K) → ℝ≥0∞ := fun y k =>
      (2 * (Fintype.card ιP : ℝ≥0∞)) * ∑ i : ιP, (‖Aamp i y k‖ₑ ^ 2 + ‖Bamp i y k‖ₑ ^ 2) with hG
  set F : AdelicGL2 (𝓞 K) K → ℝ≥0∞ := fun g => ‖EX g‖ₑ ^ 2 with hF

  have hcc : ∀ (i : ιP) (j : Fin (nE (em i))), Continuous (c i j) := fun i j => (hCIJ i j).1
  have hcI : ∀ (i : ιP) (j : Fin (nE (em i))), Integrable (c i j) := fun i j => (hCIJ i j).2.1
  have hEjc : ∀ (i : ιP) (j : Fin (nE (em i))), Continuous (fun p : ℝ × AdelicGL2 (𝓞 K) K => φE (em i) j ((((p.1 + τ i : ℝ) : ℂ)) * Complex.I) p.2) :=
    fun i j => (_hφEjc (em i) j).comp (Continuous.prodMk ((Complex.continuous_ofReal.comp (continuous_fst.add continuous_const)).mul continuous_const) continuous_snd)
  have hNjc : ∀ (i : ιP) (j : Fin (nE (em i))), Continuous (fun p : ℝ × AdelicGL2 (𝓞 K) K => NE (em i) j ((((p.1 + τ i : ℝ) : ℂ)) * Complex.I) p.2) := by
    intro i j
    have hax : ∀ t : ℝ, ((((t + τ i : ℝ) : ℂ)) * Complex.I) ∈ OE (em i) j := fun t => (_hEE (em i) j).2.2.1 (by simp)
    refine ((_hEE (em i) j).2.2.2.2.2.2.2.1).comp_continuous
      (f := fun p : ℝ × AdelicGL2 (𝓞 K) K => (((((p.1 + τ i : ℝ) : ℂ)) * Complex.I), p.2)) ?_ (fun p => ⟨hax p.1, Set.mem_univ _⟩)
    exact Continuous.prodMk ((Complex.continuous_ofReal.comp (continuous_fst.add continuous_const)).mul continuous_const) continuous_snd
  have hEXm : Measurable EX := by
    rw [hEX]
    refine Finset.measurable_sum _ fun i _ => ?_
    have hf : Measurable (fun pq : AdelicGL2 (𝓞 K) K × ℝ => ∑ j : Fin (nE (em i)), (∫ k, ψf i ((pq.2 : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((pq.2 + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
                  ∂(maximalCompactHaar K)) *
        (φE (em i) j ((((pq.2 + τ i : ℝ) : ℂ)) * Complex.I) pq.1 + ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em i) j ((((pq.2 + τ i : ℝ) : ℂ)) * Complex.I) pq.1)) := by
      refine Finset.measurable_sum _ fun j _ => ?_
      refine ((hcc i j).measurable.comp measurable_snd).mul ?_
      exact (((hEjc i j).comp (Continuous.prodMk continuous_snd continuous_fst)).add
        (continuous_const.mul ((hNjc i j).comp (Continuous.prodMk continuous_snd continuous_fst)))).measurable
    exact (hf.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))).measurable

  have hFinv : ∀ x ∈ rationalTorusUnipotent K, ∀ g : AdelicGL2 (𝓞 K) K, F (x * g) = F g := by
    intro x hx g
    have hE : EX (x * g) = EX g := by
      simp only [hEX]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1; funext t
      refine Finset.sum_congr rfl fun j _ => ?_
      obtain ⟨h1, h2⟩ := (hC1 i j t 1 1 ⟨1, one_mem _⟩).2.2 x hx g
      rw [h1, h2]
    simp only [hF, hE]

  have hφk : ∀ (i : ιP) (j : Fin (nE (em i))), Continuous fun k : ↥(adelicMaximalCompact K) => φE (em i) j 0 (k : AdelicGL2 (𝓞 K) K) :=
    fun i j => ((_hφEjc (em i) j).comp (Continuous.prodMk continuous_const continuous_id)).comp continuous_subtype_val
  have hNk : ∀ (i : ιP) (j : Fin (nE (em i))), Continuous fun p : ℝ × ↥(adelicMaximalCompact K) => NE (em i) j ((((p.1 + τ i : ℝ) : ℂ)) * Complex.I) (p.2 : AdelicGL2 (𝓞 K) K) :=
    fun i j => (hNjc i j).comp (Continuous.prodMk continuous_fst (continuous_subtype_val.comp continuous_snd))
  have hAm : ∀ i : ιP, Measurable (fun p : ℝ × ↥(adelicMaximalCompact K) => Aamp i p.1 p.2) := by
    intro i
    have hf : Measurable (fun q : (ℝ × ↥(adelicMaximalCompact K)) × ℝ => ∑ j : Fin (nE (em i)), (∫ k, ψf i ((q.2 : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((q.2 + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
                  ∂(maximalCompactHaar K)) *
        ((((q.1.1 : ℝ) : ℂ)) ^ ((((q.2 + τ i : ℝ) : ℂ)) * Complex.I) * φE (em i) j 0 (q.1.2 : AdelicGL2 (𝓞 K) K))) := by
      refine Finset.measurable_sum _ fun j _ => ?_
      refine ((hcc i j).measurable.comp measurable_snd).mul (Measurable.mul ?_ ((hφk i j).measurable.comp (measurable_snd.comp measurable_fst)))
      exact Measurable.pow (Complex.measurable_ofReal.comp (measurable_fst.comp measurable_fst))
        (((Complex.continuous_ofReal.comp (continuous_snd.add continuous_const)).mul continuous_const).measurable)
    simpa only [hA] using (hf.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))).measurable
  have hBm : ∀ i : ιP, Measurable (fun p : ℝ × ↥(adelicMaximalCompact K) => Bamp i p.1 p.2) := by
    intro i
    have hf : Measurable (fun q : (ℝ × ↥(adelicMaximalCompact K)) × ℝ => ∑ j : Fin (nE (em i)), (∫ k, ψf i ((q.2 : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((q.2 + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
                  ∂(maximalCompactHaar K)) *
        ((((q.1.1 : ℝ) : ℂ)) ^ (-((((q.2 + τ i : ℝ) : ℂ)) * Complex.I)) * (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em i) j ((((q.2 + τ i : ℝ) : ℂ)) * Complex.I) (q.1.2 : AdelicGL2 (𝓞 K) K)))) := by
      refine Finset.measurable_sum _ fun j _ => ?_
      refine ((hcc i j).measurable.comp measurable_snd).mul (Measurable.mul ?_ ?_)
      · exact Measurable.pow (Complex.measurable_ofReal.comp (measurable_fst.comp measurable_fst))
          (((Complex.continuous_ofReal.comp (continuous_snd.add continuous_const)).mul continuous_const).neg.measurable)
      · exact (continuous_const.mul ((hNk i j).comp (Continuous.prodMk continuous_snd (continuous_snd.comp continuous_fst)))).measurable
    simpa only [hB] using (hf.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))).measurable
  have hGm : Measurable (Function.uncurry G) := by
    have : Function.uncurry G = fun p : ℝ × ↥(adelicMaximalCompact K) =>
        (2 * (Fintype.card ιP : ℝ≥0∞)) * ∑ i : ιP, (‖Aamp i p.1 p.2‖ₑ ^ 2 + ‖Bamp i p.1 p.2‖ₑ ^ 2) := by
      funext p; simp only [Function.uncurry, hG]
    rw [this]
    refine Measurable.const_mul (Finset.measurable_sum _ fun i _ => ?_) _
    exact ((hAm i).enorm.pow_const 2).add ((hBm i).enorm.pow_const 2)

  have hKc : IsCompact ((adelicMaximalCompact K : Subgroup (AdelicGL2 (𝓞 K) K)) : Set (AdelicGL2 (𝓞 K) K)) := by
    have := isCompact_univ.image (continuous_subtype_val : Continuous (fun k : ↥(adelicMaximalCompact K) => (k : AdelicGL2 (𝓞 K) K)))
    rwa [Set.image_univ, Subtype.range_coe] at this
  have hreTE : ∀ (i : ιP) (t : ℝ), (((((t + τ i : ℝ) : ℂ)) * Complex.I)).re = 0 := by intro i t; simp
  have hTEc : ∀ i : ιP, Continuous fun t : ℝ => ((((t + τ i : ℝ) : ℂ)) * Complex.I) :=
    fun i => (Complex.continuous_ofReal.comp (continuous_id.add continuous_const)).mul continuous_const

  have hφbd : ∀ (i : ιP) (j : Fin (nE (em i))), ∃ Bφ : ℝ, ∀ k : ↥(adelicMaximalCompact K), ‖φE (em i) j 0 (k : AdelicGL2 (𝓞 K) K)‖ ≤ Bφ := by
    intro i j
    obtain ⟨Bφ, hB⟩ := (isCompact_univ (X := ↥(adelicMaximalCompact K))).exists_bound_of_continuousOn (hφk i j).continuousOn
    exact ⟨Bφ, fun k => hB k (Set.mem_univ _)⟩
  have hNbd : ∀ (i : ιP) (j : Fin (nE (em i))), ∃ (AN : ℝ) (nN : ℕ), ∀ (t : ℝ) (k : ↥(adelicMaximalCompact K)),
      ‖NE (em i) j ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖ ≤ AN * (1 + |t|) ^ nN := by
    intro i j
    obtain ⟨Bφ, hB⟩ := hφbd i j
    exact AutomorphicForm.exists_forall_norm_axis_continuation_weylIntertwiningIntegral_le_mul_pow_of_flat K hαm (μ (em i)) (ν (em i))
      (_hμE (em i)) (_hνE (em i)) (_hμicE (em i)) (_hνicE (em i)) (_hμcE (em i)) (_hνcE (em i)) (φE (em i) j) (_hφE (em i) j)
      (_hφEK (em i) j) (_hφEf (em i) j) (_hφEjc (em i) j) (_hφEhol (em i) j) (_hφEKu (em i) j) (OE (em i) j) (EE (em i) j) (NE (em i) j)
      (_hEE (em i) j) Bφ (fun t k => by rw [_hφEflat (em i) j _ k]; exact hB k)
  have hintB0 : ∀ (i : ιP) (j : Fin (nE (em i))) (k : ↥(adelicMaximalCompact K)),
      Integrable (fun t : ℝ => ‖c i j t‖ * ‖NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖) := by
    intro i j k
    obtain ⟨AN, nN, hAN⟩ := hNbd i j
    obtain ⟨m, hm, -, hmb⟩ := _hψdec i nN 0 _ hKc
    have hmb0 := hmb 0 (by simp)
    have hmt : ∀ t, 0 ≤ m t := fun t => le_trans (by positivity) (hmb0 t (1 : AdelicGL2 (𝓞 K) K) (one_mem _))
    have hφint : Integrable (fun k' : ↥(adelicMaximalCompact K) => ‖φE (em i) j 0 (k' : AdelicGL2 (𝓞 K) K)‖) (maximalCompactHaar K) :=
      ((hφk i j).norm).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    set I₀ : ℝ := ∫ k', ‖φE (em i) j 0 (k' : AdelicGL2 (𝓞 K) K)‖ ∂(maximalCompactHaar K) with hI₀
    have hI₀nn : 0 ≤ I₀ := integral_nonneg fun _ => norm_nonneg _
    have hcb : ∀ t : ℝ, (1 + |t|) ^ nN * ‖c i j t‖ ≤ I₀ * m t := by
      intro t
      have hpt : ∀ k' : ↥(adelicMaximalCompact K),
          (1 + |t|) ^ nN * ‖ψf i ((t : ℂ) * Complex.I) (k' : AdelicGL2 (𝓞 K) K) *
            conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k' : AdelicGL2 (𝓞 K) K))‖ ≤ m t * ‖φE (em i) j 0 (k' : AdelicGL2 (𝓞 K) K)‖ := by
        intro k'
        rw [norm_mul, RCLike.norm_conj, _hφEflat (em i) j _ k', ← mul_assoc]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        have := hmb0 t (k' : AdelicGL2 (𝓞 K) K) k'.2
        have e0 : (((0 : ℝ) : ℂ)) + ((t : ℝ) : ℂ) * Complex.I = (t : ℂ) * Complex.I := by push_cast; ring
        rwa [e0] at this
      have hint1 : Integrable (fun k' : ↥(adelicMaximalCompact K) => ψf i ((t : ℂ) * Complex.I) (k' : AdelicGL2 (𝓞 K) K) *
          conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k' : AdelicGL2 (𝓞 K) K))) (maximalCompactHaar K) :=
        ((((_hψjc i).comp (Continuous.prodMk continuous_const continuous_id)).comp continuous_subtype_val).mul
          (Complex.continuous_conj.comp ((( _hφEjc (em i) j).comp (Continuous.prodMk continuous_const continuous_id)).comp continuous_subtype_val))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      calc (1 + |t|) ^ nN * ‖c i j t‖ ≤ (1 + |t|) ^ nN * ∫ k', ‖ψf i ((t : ℂ) * Complex.I) (k' : AdelicGL2 (𝓞 K) K) *
            conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k' : AdelicGL2 (𝓞 K) K))‖ ∂(maximalCompactHaar K) := by
              simp only [hc]; exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
        _ = ∫ k', (1 + |t|) ^ nN * ‖ψf i ((t : ℂ) * Complex.I) (k' : AdelicGL2 (𝓞 K) K) *
            conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k' : AdelicGL2 (𝓞 K) K))‖ ∂(maximalCompactHaar K) := (integral_const_mul _ _).symm
        _ ≤ ∫ k', m t * ‖φE (em i) j 0 (k' : AdelicGL2 (𝓞 K) K)‖ ∂(maximalCompactHaar K) :=
              integral_mono (hint1.norm.const_mul _) (hφint.const_mul _) hpt
        _ = I₀ * m t := by rw [integral_const_mul, hI₀, mul_comm]
    have hA0 : 0 ≤ AN := by
      have h := hAN 0 ⟨1, one_mem _⟩
      simp only [abs_zero, add_zero, one_pow, mul_one] at h
      exact (norm_nonneg _).trans h
    have hcont : Continuous (fun t : ℝ => ‖c i j t‖ * ‖NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖) :=
      (hcc i j).norm.mul ((hNk i j).comp (Continuous.prodMk continuous_id continuous_const)).norm
    refine Integrable.mono' ((hm.const_mul (I₀ * (AN * (1 + |τ i|) ^ nN)))) hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : ‖NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖ ≤ AN * ((1 + |t|) * (1 + |τ i|)) ^ nN := by
      have := hAN (t + τ i) k
      refine this.trans ?_
      have h0 : 0 ≤ 1 + |t + τ i| := by positivity
      have hle : 1 + |t + τ i| ≤ (1 + |t|) * (1 + |τ i|) := by nlinarith [abs_add_le t (τ i), abs_nonneg t, abs_nonneg (τ i)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hle nN) hA0
    calc ‖c i j t‖ * ‖NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖ ≤ ‖c i j t‖ * (AN * ((1 + |t|) * (1 + |τ i|)) ^ nN) := by gcongr
      _ = (AN * (1 + |τ i|) ^ nN) * ((1 + |t|) ^ nN * ‖c i j t‖) := by rw [mul_pow]; ring
      _ ≤ (AN * (1 + |τ i|) ^ nN) * (I₀ * m t) := mul_le_mul_of_nonneg_left (hcb t) (by positivity)
      _ = I₀ * (AN * (1 + |τ i|) ^ nN) * m t := by ring

  have hbd : ∀ (z y : (AdeleRing (𝓞 K) K)ˣ) (k : ↥(adelicMaximalCompact K)),
      F (centralScalar (𝓞 K) K z * diagOne y * (k : AdelicGL2 (𝓞 K) K)) ≤
        ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K y) * G (NumberField.TateGlobal.ideleNorm K y) k := by
    intro z y k
    set n : ℝ := NumberField.TateGlobal.ideleNorm K y with hn
    have hnpos : 0 < n := NumberField.TateGlobal.ideleNorm_pos y
    have hn0 : ((n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hnpos.ne'

    have hu : ∀ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ), AutomorphicForm.IsUnitaryChar (𝓞 K) K χ → ∀ w, ‖((χ w : ℂˣ) : ℂ)‖ = 1 := fun χ hχ w => hχ w
    have hncpow : ∀ (s : ℂ), s.re = 0 → ‖((n : ℝ) : ℂ) ^ s‖ = 1 := by
      intro s hs; rw [Complex.norm_cpow_eq_rpow_re_of_pos hnpos, hs, Real.rpow_zero]
    have hnhalf : ‖((n : ℝ) : ℂ) ^ ((1 / 2 : ℂ))‖ = Real.sqrt n := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hnpos, show ((1 / 2 : ℂ)).re = 1 / 2 by norm_num, Real.sqrt_eq_rpow]

    have hintA : ∀ i : ιP, Integrable (fun t : ℝ => ∑ j : Fin (nE (em i)), c i j t *
        ((((n : ℝ) : ℂ)) ^ ((((t + τ i : ℝ) : ℂ)) * Complex.I) * φE (em i) j 0 (k : AdelicGL2 (𝓞 K) K))) := by
      intro i
      refine integrable_finsetSum _ fun j _ => ?_
      refine (hcI i j).mul_bdd (((hTEc i).const_cpow (Or.inl hn0)).mul continuous_const).aestronglyMeasurable
        (c := ‖φE (em i) j 0 (k : AdelicGL2 (𝓞 K) K)‖) (Filter.Eventually.of_forall fun t => ?_)
      rw [norm_mul, hncpow _ (hreTE i t), one_mul]
    have hintB : ∀ i : ιP, Integrable (fun t : ℝ => ∑ j : Fin (nE (em i)), c i j t *
        ((((n : ℝ) : ℂ)) ^ (-((((t + τ i : ℝ) : ℂ)) * Complex.I)) * (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)))) := by
      intro i
      refine integrable_finsetSum _ fun j _ => ?_
      have hcont : Continuous (fun t : ℝ => c i j t * ((((n : ℝ) : ℂ)) ^ (-((((t + τ i : ℝ) : ℂ)) * Complex.I)) * (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)))) :=
        (hcc i j).mul ((((hTEc i).neg).const_cpow (Or.inl hn0)).mul (continuous_const.mul ((hNk i j).comp (Continuous.prodMk continuous_id continuous_const))))
      refine Integrable.mono' ((hintB0 i j k).const_mul ‖((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹‖) hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
      rw [norm_mul, norm_mul, norm_mul, hncpow _ (by rw [Complex.neg_re, hreTE i t, neg_zero]), one_mul]
      exact le_of_eq (by ring)

    have hEXi : ∀ i : ιP, (∫ t : ℝ, ∑ j : Fin (nE (em i)), c i j t *
        (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (centralScalar (𝓞 K) K z * diagOne y * (k : AdelicGL2 (𝓞 K) K)) +
          ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (centralScalar (𝓞 K) K z * diagOne y * (k : AdelicGL2 (𝓞 K) K)))) =
        (((μ (em i) z : ℂˣ) : ℂ) * ((ν (em i) z : ℂˣ) : ℂ) * ((μ (em i) y : ℂˣ) : ℂ) * ((n : ℝ) : ℂ) ^ ((1 / 2 : ℂ))) * Aamp i n k +
        (((μ (em i) z : ℂˣ) : ℂ) * ((ν (em i) z : ℂˣ) : ℂ) * ((ν (em i) y : ℂˣ) : ℂ) * ((n : ℝ) : ℂ) ^ ((1 / 2 : ℂ))) * Bamp i n k := by
      intro i
      have hptw : ∀ t : ℝ, (∑ j : Fin (nE (em i)), c i j t *
          (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (centralScalar (𝓞 K) K z * diagOne y * (k : AdelicGL2 (𝓞 K) K)) +
            ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (centralScalar (𝓞 K) K z * diagOne y * (k : AdelicGL2 (𝓞 K) K)))) =
          (((μ (em i) z : ℂˣ) : ℂ) * ((ν (em i) z : ℂˣ) : ℂ) * ((μ (em i) y : ℂˣ) : ℂ) * ((n : ℝ) : ℂ) ^ ((1 / 2 : ℂ))) *
            (∑ j : Fin (nE (em i)), c i j t * ((((n : ℝ) : ℂ)) ^ ((((t + τ i : ℝ) : ℂ)) * Complex.I) * φE (em i) j 0 (k : AdelicGL2 (𝓞 K) K))) +
          (((μ (em i) z : ℂˣ) : ℂ) * ((ν (em i) z : ℂˣ) : ℂ) * ((ν (em i) y : ℂˣ) : ℂ) * ((n : ℝ) : ℂ) ^ ((1 / 2 : ℂ))) *
            (∑ j : Fin (nE (em i)), c i j t * ((((n : ℝ) : ℂ)) ^ (-((((t + τ i : ℝ) : ℂ)) * Complex.I)) * (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)))) := by
        intro t
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        obtain ⟨h1, h2, -⟩ := hC1 i j t z y k
        rw [h1, h2, Complex.cpow_add _ _ hn0, Complex.cpow_add _ _ hn0]
        simp only [hn]
        ring
      simp_rw [hptw]
      rw [integral_add ((hintA i).const_mul _) ((hintB i).const_mul _), integral_const_mul, integral_const_mul]

    have hnormi : ∀ i : ιP, ‖∫ t : ℝ, ∑ j : Fin (nE (em i)), c i j t *
        (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (centralScalar (𝓞 K) K z * diagOne y * (k : AdelicGL2 (𝓞 K) K)) +
          ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (centralScalar (𝓞 K) K z * diagOne y * (k : AdelicGL2 (𝓞 K) K)))‖ ≤
        Real.sqrt n * (‖Aamp i n k‖ + ‖Bamp i n k‖) := by
      intro i
      rw [hEXi i]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul,
        hu _ (_hμE (em i)), hu _ (_hνE (em i)), hu _ (_hμE (em i)), hu _ (_hνE (em i)), hnhalf]
      exact le_of_eq (by ring)
    have hEXpt : EX (centralScalar (𝓞 K) K z * diagOne y * (k : AdelicGL2 (𝓞 K) K)) =
        ∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)), c i j t *
          (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (centralScalar (𝓞 K) K z * diagOne y * (k : AdelicGL2 (𝓞 K) K)) +
            ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (centralScalar (𝓞 K) K z * diagOne y * (k : AdelicGL2 (𝓞 K) K))) := by
      simp only [hEX, hc]
    have hEXnorm : ‖EX (centralScalar (𝓞 K) K z * diagOne y * (k : AdelicGL2 (𝓞 K) K))‖ ≤
        Real.sqrt n * ∑ i : ιP, (‖Aamp i n k‖ + ‖Bamp i n k‖) := by
      rw [hEXpt, Finset.mul_sum]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hnormi i)
    have hreal : ‖EX (centralScalar (𝓞 K) K z * diagOne y * (k : AdelicGL2 (𝓞 K) K))‖ ^ 2 ≤
        n * (2 * (Fintype.card ιP : ℝ) * ∑ i : ιP, (‖Aamp i n k‖ ^ 2 + ‖Bamp i n k‖ ^ 2)) := by
      have h1 : ‖EX (centralScalar (𝓞 K) K z * diagOne y * (k : AdelicGL2 (𝓞 K) K))‖ ^ 2 ≤
          (Real.sqrt n * ∑ i : ιP, (‖Aamp i n k‖ + ‖Bamp i n k‖)) ^ 2 := by gcongr
      have h2 : (∑ i : ιP, (‖Aamp i n k‖ + ‖Bamp i n k‖)) ^ 2 ≤
          (Fintype.card ιP : ℝ) * ∑ i : ιP, (‖Aamp i n k‖ + ‖Bamp i n k‖) ^ 2 := by
        have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : ιP => ‖Aamp i n k‖ + ‖Bamp i n k‖)
        simpa using this
      have h3 : ∑ i : ιP, (‖Aamp i n k‖ + ‖Bamp i n k‖) ^ 2 ≤ ∑ i : ιP, 2 * (‖Aamp i n k‖ ^ 2 + ‖Bamp i n k‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (‖Aamp i n k‖ - ‖Bamp i n k‖)]
      calc _ ≤ (Real.sqrt n * ∑ i : ιP, (‖Aamp i n k‖ + ‖Bamp i n k‖)) ^ 2 := h1
        _ = n * (∑ i : ιP, (‖Aamp i n k‖ + ‖Bamp i n k‖)) ^ 2 := by rw [mul_pow, Real.sq_sqrt hnpos.le]
        _ ≤ n * ((Fintype.card ιP : ℝ) * ∑ i : ιP, 2 * (‖Aamp i n k‖ ^ 2 + ‖Bamp i n k‖ ^ 2)) := by
            gcongr
            exact h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
        _ = n * (2 * (Fintype.card ιP : ℝ) * ∑ i : ιP, (‖Aamp i n k‖ ^ 2 + ‖Bamp i n k‖ ^ 2)) := by
            rw [← Finset.mul_sum]; ring

    have hF' : F (centralScalar (𝓞 K) K z * diagOne y * (k : AdelicGL2 (𝓞 K) K)) =
        ENNReal.ofReal (‖EX (centralScalar (𝓞 K) K z * diagOne y * (k : AdelicGL2 (𝓞 K) K))‖ ^ 2) := by
      simp only [hF]; rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
    have hG' : G n k = ENNReal.ofReal (2 * (Fintype.card ιP : ℝ) * ∑ i : ιP, (‖Aamp i n k‖ ^ 2 + ‖Bamp i n k‖ ^ 2)) := by
      simp only [hG]
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
      congr 1
      · rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_pow (norm_nonneg _),
          ofReal_norm, ofReal_norm]
    rw [hF', hG', ← ENNReal.ofReal_mul hnpos.le]
    exact ENNReal.ofReal_le_ofReal hreal

  have hmain : ∫⁻ g in AutomorphicForm.canonicalTruncationDomain K α β ∩
      {g | Real.exp R < NumberField.AdelicHeight.adelicHeight K g}, F g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) < ⊤ := by
    have h := hC3 (Real.exp R) F ((hEXm.enorm).pow_const 2) hFinv G hGm hbd
    refine lt_of_le_of_lt h ?_
    refine ENNReal.mul_lt_top hC3ne.lt_top ?_

    have hsplit : ∀ k : ↥(adelicMaximalCompact K), (∫⁻ y in Set.Ioi (0 : ℝ), G y k * ENNReal.ofReal y⁻¹ ∂volume) =
        (2 * (Fintype.card ιP : ℝ≥0∞)) * ∑ i : ιP,
          ((∫⁻ y in Set.Ioi (0 : ℝ), ‖Aamp i y k‖ₑ ^ 2 * ENNReal.ofReal y⁻¹ ∂volume) +
           (∫⁻ y in Set.Ioi (0 : ℝ), ‖Bamp i y k‖ₑ ^ 2 * ENNReal.ofReal y⁻¹ ∂volume)) := by
      intro k
      have hw : Measurable fun y : ℝ => ENNReal.ofReal y⁻¹ := ENNReal.measurable_ofReal.comp measurable_inv
      have hAk : ∀ i, Measurable fun y : ℝ => ‖Aamp i y k‖ₑ ^ 2 * ENNReal.ofReal y⁻¹ :=
        fun i => (((hAm i).comp (measurable_id.prodMk measurable_const)).enorm.pow_const 2).mul hw
      have hBk : ∀ i, Measurable fun y : ℝ => ‖Bamp i y k‖ₑ ^ 2 * ENNReal.ofReal y⁻¹ :=
        fun i => (((hBm i).comp (measurable_id.prodMk measurable_const)).enorm.pow_const 2).mul hw
      have hpt : ∀ y : ℝ, G y k * ENNReal.ofReal y⁻¹ = (2 * (Fintype.card ιP : ℝ≥0∞)) *
          ∑ i : ιP, (‖Aamp i y k‖ₑ ^ 2 * ENNReal.ofReal y⁻¹ + ‖Bamp i y k‖ₑ ^ 2 * ENNReal.ofReal y⁻¹) := by
        intro y; simp only [hG, Finset.sum_mul, add_mul, mul_assoc]
      simp_rw [hpt]
      rw [lintegral_const_mul _ (Finset.measurable_sum _ fun i _ => (hAk i).fun_add (hBk i)),
        lintegral_finsetSum _ (fun i _ => (hAk i).fun_add (hBk i))]
      congr 1
      exact Finset.sum_congr rfl fun i _ => lintegral_add_left (hAk i) _
    simp_rw [hsplit]
    have hIk : ∀ i, Measurable fun k : ↥(adelicMaximalCompact K) =>
        (∫⁻ y in Set.Ioi (0 : ℝ), ‖Aamp i y k‖ₑ ^ 2 * ENNReal.ofReal y⁻¹ ∂volume) +
        (∫⁻ y in Set.Ioi (0 : ℝ), ‖Bamp i y k‖ₑ ^ 2 * ENNReal.ofReal y⁻¹ ∂volume) := by
      intro i
      have hw : Measurable fun p : ℝ × ↥(adelicMaximalCompact K) => ENNReal.ofReal (p.1)⁻¹ :=
        ENNReal.measurable_ofReal.comp (measurable_inv.comp measurable_fst)
      exact ((((hAm i).enorm.pow_const 2).mul hw).lintegral_prod_left'
        (μ := (volume : Measure ℝ).restrict (Set.Ioi 0))).add
        ((((hBm i).enorm.pow_const 2).mul hw).lintegral_prod_left' (μ := (volume : Measure ℝ).restrict (Set.Ioi 0)))
    rw [lintegral_const_mul _ (Finset.measurable_sum _ fun i _ => hIk i),
      lintegral_finsetSum _ (fun i _ => hIk i)]
    refine ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) (by simp)) ?_
    refine (ENNReal.sum_lt_top).mpr fun i _ => ?_
    have hw : Measurable fun p : ℝ × ↥(adelicMaximalCompact K) => ENNReal.ofReal (p.1)⁻¹ :=
      ENNReal.measurable_ofReal.comp (measurable_inv.comp measurable_fst)
    rw [lintegral_add_left ((((hAm i).enorm.pow_const 2).fun_mul hw).lintegral_prod_left' (μ := (volume : Measure ℝ).restrict (Set.Ioi 0)))]
    have h2 := hC2 i
    exact ENNReal.add_lt_top.mpr ⟨by simpa only [hA] using h2.1, by simpa only [hB] using h2.2⟩

  have hsM : MeasurableSet (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)) :=
    (isOpen_lt continuous_const (NumberField.AdelicHeight.continuous_adelicHeight K)).measurableSet
  have haesm : AEStronglyMeasurable (fun g : AdelicGL2 (𝓞 K) K =>
      (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)).indicator EX g) ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) :=
    (hEXm.indicator hsM).aestronglyMeasurable
  refine ⟨haesm, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
  refine ENNReal.rpow_lt_top_of_nonneg (by positivity) (lt_top_iff_ne_top.mp ?_)
  have hpt : ∀ g : AdelicGL2 (𝓞 K) K,
      ‖(AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)).indicator EX g‖ₑ ^ (2 : ℝ≥0∞).toReal =
        (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)).indicator F g := by
    intro g
    rw [ENNReal.toReal_ofNat, ENNReal.rpow_two]
    by_cases hg : g ∈ AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
    · simp only [Set.indicator_of_mem hg, hF]
    · simp only [Set.indicator_of_notMem hg, enorm_zero, hF]
      simp
  simp_rw [hpt]
  rw [lintegral_indicator hsM, Measure.restrict_restrict hsM]
  have hset : AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R) ∩ AutomorphicForm.canonicalTruncationDomain K α β =
      AutomorphicForm.canonicalTruncationDomain K α β ∩ {g | Real.exp R < NumberField.AdelicHeight.adelicHeight K g} := by
    rw [Set.inter_comm]; rfl
  rw [hset]
  exact hmain

end S_AutomorphicForm_exists_forall_memLp_two_indicator_highSet_sum_integral_sum_inner_mul_add_inv_vol_mul_axis_continuation_weylIntertwining_of_matched_paleyWiener
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_memLp_two_indicator_highSet_sum_integral_sum_inner_mul_add_inv_vol_mul_axis_continuation_weylIntertwining_of_matched_paleyWiener (solution)
