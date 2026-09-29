-- Prove2me | solution 1 for AutomorphicForm.forall_axis_continuation_sub_sum_mul_axis_continuation_eq_zero_of_forall_constantTerm_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/051ff034-f13b-55ac-8026-9a1df8ec21e6

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
import Theorems.Thm_AutomorphicForm_axis_continuation_bruhatEisenstein_globalPoints_mul_eq_of_isArchKFinite_family
import Theorems.Thm_AutomorphicForm_axis_continuation_bruhatEisenstein_centralScalar_mul_eq_of_isArchKFinite_family
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_AutomorphicForm_exists_pos_forall_le_adelicHeight_and_adelicHeight_globalPoints_mul_le_inv_of_mem_canonicalTruncationDomain
import Theorems.Thm_AutomorphicForm_axis_continuation_bruhatEisenstein_mul_principalLevel_eq_of_isArchKFinite_family
import Theorems.Thm_AutomorphicForm_isKfSmooth_axis_continuation_bruhatEisenstein_of_principalLevel_of_isArchKFinite_family
import Theorems.Thm_AutomorphicForm_axis_continuation_bruhatEisenstein_mem_archCutSubmodule_of_forall_mem_archCutSubmodule
import Theorems.Thm_AutomorphicForm_forall_exists_forall_norm_le_mul_inv_adelicHeight_pow_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule
import Theorems.Thm_AutomorphicForm_exists_norm_constantTerm_axis_continuation_le_mul_adelicHeight_rpow_of_mem_of_mem_canonicalTruncationDomain
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_exists_norm_lambdaT_axis_continuation_le_mul_adelicHeight_rpow_neg_of_mem_of_mem_canonicalTruncationDomain
import Theorems.Thm_AutomorphicForm_setIntegral_axis_continuation_mul_conj_cuspBasis_eq_zero_of_mem
import Theorems.Thm_AutomorphicForm_forall_eq_zero_of_ae_prod_restrict_eq_zero_of_apply_globalPoints_mul_of_apply_centralScalar_mul_of_isFundamentalDomain_slab
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_forall_axis_continuation_sub_sum_mul_axis_continuation_eq_zero_of_forall_constantTerm_eq_zero
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.CuspidalConstituent.rightRegular_apply AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.iotaZsqrtdNegTwo_apply EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22LocalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_right ContinuousAddEquiv.preimage_mulLeft_smul"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

set_option maxHeartbeats 1600000 in
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
      (e ē : ιE) (σ : ℝ)
      (_hsw : μ ē = ν e * NumberField.TateGlobal.normPowChar K σ ∧
        ν ē = μ e * (NumberField.TateGlobal.normPowChar K σ)⁻¹)
      (j : Fin (nE e)) (t : ℝ) (c : Fin (nE ē) → ℂ)
      (_hCT : ∀ g : AdelicGL2 (𝓞 K) K,
        AutomorphicForm.constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
          (fun u => AutomorphicForm.unipotentGL2 u)
          (fun x : AdelicGL2 (𝓞 K) K => (EE e j ((t : ℂ) * Complex.I) x -
          ∑ j' : Fin (nE ē), c j' * EE ē j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) x)) g = 0)
      (g : AdelicGL2 (𝓞 K) K),
    (EE e j ((t : ℂ) * Complex.I) g -
          ∑ j' : Fin (nE ē), c j' * EE ē j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) g) = 0 := by
  intro αm hαm ι b cls hb hbn hbo hbs hbc ιE _ μ ν hμ hν hμic hνic hμc hνc hμν hdist nE φE hφE hφEK hφEf hφEjc hφEhol hφEKu
    hφEflat hφElev hφEty hφEon hφEspan hpairs OE EE NE hEE e ē σ hsw j t c hCT g

  set D : AdelicGL2 (𝓞 K) K → ℂ := (fun x : AdelicGL2 (𝓞 K) K => (EE e j ((t : ℂ) * Complex.I) x -
          ∑ j' : Fin (nE ē), c j' * EE ē j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) x)) with hD

  have S1 : AutomorphicForm.IsLsXiFunction (𝓞 K) K (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) ξK D := by

    have hax : ∀ (e₀ : ιE) (j₀ : Fin (nE e₀)) (s₀ : ℂ), s₀.re = 0 → s₀ ∈ OE e₀ j₀ :=
      fun e₀ j₀ s₀ hs₀ => (hEE e₀ j₀).2.2.1 hs₀
    have hΓ : ∀ (e₀ : ιE) (j₀ : Fin (nE e₀)) (s₀ : ℂ), s₀.re = 0 → ∀ (γ : GL (Fin 2) K) (x : AdelicGL2 (𝓞 K) K),
        EE e₀ j₀ s₀ (AutomorphicForm.globalPoints (𝓞 K) K γ * x) = EE e₀ j₀ s₀ x :=
      fun e₀ j₀ s₀ hs₀ γ x =>
        AutomorphicForm.axis_continuation_bruhatEisenstein_globalPoints_mul_eq_of_isArchKFinite_family K hαm
          (μ e₀) (ν e₀) (hμ e₀) (hν e₀) (hμic e₀) (hνic e₀) (hμc e₀) (hνc e₀) (φE e₀ j₀) (hφE e₀ j₀) (hφEK e₀ j₀)
          (hφEf e₀ j₀) (hφEjc e₀ j₀) (hφEhol e₀ j₀) (hφEKu e₀ j₀) (OE e₀ j₀) (EE e₀ j₀) (NE e₀ j₀) (hEE e₀ j₀)
          s₀ (hax e₀ j₀ s₀ hs₀) γ x
    have hZ : ∀ (e₀ : ιE) (j₀ : Fin (nE e₀)) (s₀ : ℂ), s₀.re = 0 → ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (x : AdelicGL2 (𝓞 K) K),
        EE e₀ j₀ s₀ (AutomorphicForm.centralScalar (𝓞 K) K z * x) = ((μ e₀ z : ℂˣ) : ℂ) * ((ν e₀ z : ℂˣ) : ℂ) * EE e₀ j₀ s₀ x :=
      fun e₀ j₀ s₀ hs₀ z x =>
        AutomorphicForm.axis_continuation_bruhatEisenstein_centralScalar_mul_eq_of_isArchKFinite_family K hαm
          (μ e₀) (ν e₀) (hμ e₀) (hν e₀) (hμic e₀) (hνic e₀) (hμc e₀) (hνc e₀) (φE e₀ j₀) (hφE e₀ j₀) (hφEK e₀ j₀)
          (hφEf e₀ j₀) (hφEjc e₀ j₀) (hφEhol e₀ j₀) (hφEKu e₀ j₀) (OE e₀ j₀) (EE e₀ j₀) (NE e₀ j₀) (hEE e₀ j₀)
          s₀ (hax e₀ j₀ s₀ hs₀) z x
    have hξ : ∀ (e₀ : ιE) (z : (AdeleRing (𝓞 K) K)ˣ),
        ((μ e₀ z : ℂˣ) : ℂ) * ((ν e₀ z : ℂˣ) : ℂ) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) := by
      intro e₀ z; rw [← Units.val_mul, hμν e₀ z]
    have hre1 : (((t : ℂ) * Complex.I)).re = 0 := by simp
    have hre2 : ((-((((t + σ : ℝ) : ℂ)) * Complex.I))).re = 0 := by simp
    refine ⟨fun γ x => ?_, fun z x => ?_⟩
    · simp only [hD, hΓ e j ((t : ℂ) * Complex.I) hre1 γ x, fun j' => hΓ ē j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) hre2 γ x]
    · rcases z with ⟨z, hz⟩
      simp only [hD, hZ e j ((t : ℂ) * Complex.I) hre1 z x, fun j' => hZ ē j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) hre2 z x, hξ]
      rw [mul_sub, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl (fun _ _ => by ring)

  have S2 : Continuous D := by
    have hcontE : ∀ (e₀ : ιE) (j₀ : Fin (nE e₀)) (s₀ : ℂ), s₀.re = 0 →
        Continuous (fun x : AdelicGL2 (𝓞 K) K => EE e₀ j₀ s₀ x) := by
      intro e₀ j₀ s₀ hs₀
      obtain ⟨-, -, hax, -, -, -, hcont, -⟩ := hEE e₀ j₀
      have hmem : s₀ ∈ OE e₀ j₀ := hax hs₀
      exact hcont.comp_continuous (continuous_const.prodMk continuous_id) (fun x => ⟨hmem, Set.mem_univ _⟩)
    have h1 := hcontE e j ((t : ℂ) * Complex.I) (by simp)
    have h2 : ∀ j' : Fin (nE ē), Continuous (fun x : AdelicGL2 (𝓞 K) K =>
        c j' * EE ē j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) x) :=
      fun j' => continuous_const.mul (hcontE ē j' _ (by simp))
    rw [hD]
    exact h1.sub (continuous_finsetSum _ (fun j' _ => h2 j'))
  have hre1 : (((t : ℂ) * Complex.I)).re = 0 := by simp
  have hre2 : ((-((((t + σ : ℝ) : ℂ)) * Complex.I))).re = 0 := by simp
  have hax : ∀ (e₀ : ιE) (j₀ : Fin (nE e₀)) (s₀ : ℂ), s₀.re = 0 → s₀ ∈ OE e₀ j₀ :=
    fun e₀ j₀ s₀ hs₀ => (hEE e₀ j₀).2.2.1 hs₀

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

  have S3 : ∀ x : AdelicGL2 (𝓞 K) K, ∀ u ∈ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).U N, D (x * u) = D x := by
    intro x u hu
    have hL : ∀ (e₀ : ιE) (j₀ : Fin (nE e₀)) (s₀ : ℂ), s₀.re = 0 → EE e₀ j₀ s₀ (x * u) = EE e₀ j₀ s₀ x :=
      fun e₀ j₀ s₀ hs₀ =>
        AutomorphicForm.axis_continuation_bruhatEisenstein_mul_principalLevel_eq_of_isArchKFinite_family
          K hαm (μ e₀) (ν e₀) (hμ e₀) (hν e₀) (hμic e₀) (hνic e₀) (hμc e₀) (hνc e₀) (φE e₀ j₀) (hφE e₀ j₀) (hφEK e₀ j₀)
          (hφEf e₀ j₀) (hφEjc e₀ j₀) (hφEhol e₀ j₀) (hφEKu e₀ j₀) N (hφElev e₀ j₀) (OE e₀ j₀) (EE e₀ j₀) (NE e₀ j₀) (hEE e₀ j₀) s₀ (hax e₀ j₀ s₀ hs₀) x u hu
    simp only [hD, hL e j _ hre1, fun j' => hL ē j' _ hre2]

  have S4 : D ∈ archCutSubmodule K tysK := by
    have hA : ∀ (e₀ : ιE) (j₀ : Fin (nE e₀)) (s₀ : ℂ), s₀.re = 0 → EE e₀ j₀ s₀ ∈ archCutSubmodule K tysK :=
      fun e₀ j₀ s₀ hs₀ =>
        AutomorphicForm.axis_continuation_bruhatEisenstein_mem_archCutSubmodule_of_forall_mem_archCutSubmodule
          K hαm (μ e₀) (ν e₀) (hμ e₀) (hν e₀) (hμic e₀) (hνic e₀) (hμc e₀) (hνc e₀) (φE e₀ j₀) (hφE e₀ j₀) (hφEK e₀ j₀)
          (hφEf e₀ j₀) (hφEjc e₀ j₀) (hφEhol e₀ j₀) (hφEKu e₀ j₀) tysK (hφEty e₀ j₀) (OE e₀ j₀) (EE e₀ j₀) (NE e₀ j₀) (hEE e₀ j₀) s₀ (hax e₀ j₀ s₀ hs₀)
    have hDv : D = EE e j ((t : ℂ) * Complex.I) - ∑ j' : Fin (nE ē), c j' • EE ē j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) := by
      funext x
      simp only [hD, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hDv]
    exact Submodule.sub_mem _ (hA e j _ hre1)
      (Submodule.sum_mem _ fun j' _ => Submodule.smul_mem _ _ (hA ē j' _ hre2))

  have S5 : IsKfSmooth K D := by
    have hKf : ∀ (e₀ : ιE) (j₀ : Fin (nE e₀)) (s₀ : ℂ), s₀.re = 0 → IsKfSmooth K (EE e₀ j₀ s₀) :=
      fun e₀ j₀ s₀ hs₀ =>
        AutomorphicForm.isKfSmooth_axis_continuation_bruhatEisenstein_of_principalLevel_of_isArchKFinite_family
          K hαm (μ e₀) (ν e₀) (hμ e₀) (hν e₀) (hμic e₀) (hνic e₀) (hμc e₀) (hνc e₀) (φE e₀ j₀) (hφE e₀ j₀) (hφEK e₀ j₀)
          (hφEf e₀ j₀) (hφEjc e₀ j₀) (hφEhol e₀ j₀) (hφEKu e₀ j₀) N (hφElev e₀ j₀) hNbot (OE e₀ j₀) (EE e₀ j₀) (NE e₀ j₀) (hEE e₀ j₀) s₀ (hax e₀ j₀ s₀ hs₀)
    classical
    obtain ⟨U, hUo, hU⟩ := FLT.SmoothVectors.exists_isOpen_subgroup_forall_smul_eq
      (G := ↥(finiteAdelicGL2Subgroup K)) (Finset.univ : Finset (Option (Fin (nE ē))))
      (fun o => (FLT.SmoothVectors.RightTranslationFn.mk
        (Option.elim o (EE e j ((t : ℂ) * Complex.I)) (fun j' => EE ē j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)))) : FLT.SmoothVectors.RightTranslationFn (AdelicGL2 (𝓞 K) K) ℂ))
      (fun o _ => by
        cases o with
        | none => exact hKf e j _ hre1
        | some j' => exact hKf ē j' _ hre2)
    rw [AutomorphicForm.isKfSmooth_iff, FLT.SmoothVectors.isSmoothVector_iff_isOpen_stabilizer]
    refine Subgroup.isOpen_mono (H₁ := U) (fun u hu => ?_) hUo
    rw [MulAction.mem_stabilizer_iff]
    refine FLT.SmoothVectors.RightTranslationFn.ext fun x => ?_
    have h1 := congrArg (fun f => FLT.SmoothVectors.RightTranslationFn.toFun f x) (hU none (Finset.mem_univ _) u hu)
    have h2 := fun j' : Fin (nE ē) =>
      congrArg (fun f => FLT.SmoothVectors.RightTranslationFn.toFun f x) (hU (some j') (Finset.mem_univ _) u hu)
    simp only [Subgroup.smul_def, FLT.SmoothVectors.RightTranslationFn.toFun_smul,
      FLT.SmoothVectors.RightTranslationFn.toFun_mk, Option.elim_none, Option.elim_some] at h1 h2 ⊢
    show D (x * ↑u) = D x
    simp only [hD, h1, h2]

  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := adeleBorel (𝓞 K) K
  haveI : BorelSpace (AdeleRing (𝓞 K) K) := borelSpace_adeleBorel (𝓞 K) K
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 K) K
  have hcontE : ∀ (e₀ : ιE) (j₀ : Fin (nE e₀)) (s₀ : ℂ), s₀.re = 0 →
      Continuous (fun x : AdelicGL2 (𝓞 K) K => EE e₀ j₀ s₀ x) := by
    intro e₀ j₀ s₀ hs₀
    obtain ⟨-, -, hax', -, -, -, hcont, -⟩ := hEE e₀ j₀
    exact hcont.comp_continuous (continuous_const.prodMk continuous_id) (fun x => ⟨hax' hs₀, Set.mem_univ _⟩)

  have hu : Continuous fun q : AdeleRing (𝓞 K) K => (AutomorphicForm.unipotentGL2 q : AdelicGL2 (𝓞 K) K) := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · refine continuous_matrix fun i j => ?_
      fin_cases i <;> fin_cases j <;>
        simp [AutomorphicForm.unipotentGL2] <;> first | exact continuous_const | exact continuous_id
    · have h : ∀ q : AdeleRing (𝓞 K) K,
          (((AutomorphicForm.unipotentGL2 q)⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
            !![1, -q; 0, 1] := fun q => rfl
      simp_rw [h]
      refine continuous_matrix fun i j => ?_
      fin_cases i <;> fin_cases j <;>
        simp <;> first | exact continuous_const | exact continuous_id | exact continuous_neg

  have hint : ∀ (φ : AdelicGL2 (𝓞 K) K → ℂ), Continuous φ → ∀ x : AdelicGL2 (𝓞 K) K,
      Integrable (fun q : AdeleRing (𝓞 K) K => φ (AutomorphicForm.unipotentGL2 q * x))
        (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)) := by
    intro φ hφ x
    have hcont : Continuous (fun q : AdeleRing (𝓞 K) K => φ (AutomorphicForm.unipotentGL2 q * x)) :=
      hφ.comp (hu.mul continuous_const)
    obtain ⟨C, hC, hsub⟩ := exists_isCompact_adelicBox_subset K
    have hI : IntegrableOn (fun q : AdeleRing (𝓞 K) K => φ (AutomorphicForm.unipotentGL2 q * x)) (adelicBox K)
        (adelicAddHaar (𝓞 K) K) :=
      (hcont.continuousOn.integrableOn_compact hC).mono_set hsub
    rw [ProbabilityTheory.cond]
    exact hI.smul_measure (ENNReal.inv_ne_top.mpr (adelicAddHaar_adelicBox_pos K).ne')

  have h44 : ∀ (e₀ : ιE) (j₀ : Fin (nE e₀)) (s₀ : ℂ), s₀.re = 0 → ∃ M : ℝ, ∀ x ∈ AutomorphicForm.canonicalTruncationDomain K α β,
      ‖EE e₀ j₀ s₀ x - AutomorphicForm.constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)) (fun u => AutomorphicForm.unipotentGL2 u) (EE e₀ j₀ s₀) x‖ ≤ M := by
    intro e₀ j₀ s₀ hs₀
    obtain ⟨M, hM⟩ :=
      AutomorphicForm.exists_norm_lambdaT_axis_continuation_le_mul_adelicHeight_rpow_neg_of_mem_of_mem_canonicalTruncationDomain
        K α β hα hαβ (AutomorphicForm.canonicalTruncationDomain K α β) hαm (μ e₀) (ν e₀) (hμ e₀) (hν e₀) (hμic e₀) (hνic e₀) (hμc e₀) (hνc e₀)
        (φE e₀ j₀) (hφE e₀ j₀) (hφEK e₀ j₀) (hφEf e₀ j₀) (hφEjc e₀ j₀) (hφEhol e₀ j₀) (hφEKu e₀ j₀)
        (OE e₀ j₀) (EE e₀ j₀) (NE e₀ j₀) (hEE e₀ j₀) s₀ (hax e₀ j₀ s₀ hs₀) 0
    refine ⟨M, fun x hx => ?_⟩
    have hH : 0 < NumberField.AdelicHeight.adelicHeight K x := NumberField.AdelicHeight.adelicHeight_pos x
    have hR : Real.exp (Real.log (NumberField.AdelicHeight.adelicHeight K x / 2)) < NumberField.AdelicHeight.adelicHeight K x := by
      rw [Real.exp_log (half_pos hH)]; exact half_lt_self hH
    have hb := hM (Real.log (NumberField.AdelicHeight.adelicHeight K x / 2)) x hx hR
    rw [AutomorphicForm.lambdaT_apply_of_lt _ _ hR] at hb
    simp at hb
    exact hb

  have h00 : ∀ (e₀ : ιE) (j₀ : Fin (nE e₀)) (s₀ : ℂ), s₀.re = 0 → ∃ M A : ℝ, ∀ x ∈ AutomorphicForm.canonicalTruncationDomain K α β,
      ‖AutomorphicForm.constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)) (fun u => AutomorphicForm.unipotentGL2 u) (EE e₀ j₀ s₀) x‖ ≤ M * (NumberField.AdelicHeight.adelicHeight K x) ^ A := by
    intro e₀ j₀ s₀ hs₀
    obtain ⟨M, A, hMA⟩ :=
      AutomorphicForm.exists_norm_constantTerm_axis_continuation_le_mul_adelicHeight_rpow_of_mem_of_mem_canonicalTruncationDomain
        K α β hα hαβ (AutomorphicForm.canonicalTruncationDomain K α β) hαm (μ e₀) (ν e₀) (hμ e₀) (hν e₀) (hμic e₀) (hνic e₀) (hμc e₀) (hνc e₀)
        (φE e₀ j₀) (hφE e₀ j₀) (hφEK e₀ j₀) (hφEf e₀ j₀) (hφEjc e₀ j₀) (hφEhol e₀ j₀) (hφEKu e₀ j₀)
        (OE e₀ j₀) (EE e₀ j₀) (NE e₀ j₀) (hEE e₀ j₀) s₀ (hax e₀ j₀ s₀ hs₀)
    exact ⟨M, A, fun x hx => hMA x hx⟩

  obtain ⟨-, -, -, hΦs, hΦ⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ
  have hfin : adelicGLHaar (Fin 2) (𝓞 K) K (AutomorphicForm.canonicalTruncationDomain K α β) < ⊤ := by
    have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
      K α β hα hαβ (AutomorphicForm.canonicalTruncationDomain K α β) hΦ
    rwa [Set.inter_eq_left.mpr hΦs] at h
  haveI : IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  have hmem : ∀ᵐ x ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)), x ∈ AutomorphicForm.canonicalTruncationDomain K α β := by
    have h1 : ∀ᵐ x ∂(((adelicGLHaar (Fin 2) (𝓞 K) K).restrict {g : AdelicGL2 (𝓞 K) K | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}).restrict (AutomorphicForm.canonicalTruncationDomain K α β)), x ∈ AutomorphicForm.canonicalTruncationDomain K α β :=
      ae_restrict_mem₀ hΦ.nullMeasurableSet
    rwa [Measure.restrict_restrict_of_subset hΦs] at h1

  obtain ⟨h₀, h₀pos, hfloor, -⟩ :=
    AutomorphicForm.exists_pos_forall_le_adelicHeight_and_adelicHeight_globalPoints_mul_le_inv_of_mem_canonicalTruncationDomain
      K α β hα hαβ

  have hbcont : ∀ i : ι, Continuous (b i) := by
    intro i
    refine Submodule.span_induction (p := fun φ _ => Continuous φ) (fun φ hφ => hφ.continuous) continuous_const
      (fun _ _ _ _ hu' hw' => hu'.add hw') (fun a _ _ hu' => hu'.const_smul a) (Submodule.mem_inf.mp (hb i).2).1

  have S6 : MemLp D 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := by
    have hI1 : ∀ x : AdelicGL2 (𝓞 K) K, Integrable (fun q : AdeleRing (𝓞 K) K => EE e j ((t : ℂ) * Complex.I) (AutomorphicForm.unipotentGL2 q * x))
        (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)) :=
      fun x => hint _ (hcontE e j _ hre1) x
    have hI2 : ∀ (x : AdelicGL2 (𝓞 K) K) (j' : Fin (nE ē)), Integrable
        (fun q : AdeleRing (𝓞 K) K => c j' * EE ē j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) (AutomorphicForm.unipotentGL2 q * x))
        (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)) :=
      fun x j' => (hint _ (hcontE ē j' _ hre2) x).const_mul (c j')
    have hCTlin : ∀ x : AdelicGL2 (𝓞 K) K, AutomorphicForm.constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)) (fun u => AutomorphicForm.unipotentGL2 u) D x =
        AutomorphicForm.constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)) (fun u => AutomorphicForm.unipotentGL2 u) (EE e j ((t : ℂ) * Complex.I)) x - ∑ j' : Fin (nE ē), c j' * AutomorphicForm.constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)) (fun u => AutomorphicForm.unipotentGL2 u) (EE ē j' (-((((t + σ : ℝ) : ℂ)) * Complex.I))) x := by
      intro x
      have hexp : AutomorphicForm.constantTermIntegrand (fun u : AdeleRing (𝓞 K) K => AutomorphicForm.unipotentGL2 u) D x =
          fun q : AdeleRing (𝓞 K) K => EE e j ((t : ℂ) * Complex.I) (AutomorphicForm.unipotentGL2 q * x) -
            ∑ j' : Fin (nE ē), c j' * EE ē j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) (AutomorphicForm.unipotentGL2 q * x) := by
        funext q; simp only [AutomorphicForm.constantTermIntegrand, hD]
      unfold AutomorphicForm.constantTerm
      rw [hexp, integral_sub (hI1 x) (integrable_finset_sum _ (fun j' _ => hI2 x j')),
        integral_finset_sum _ (fun j' _ => hI2 x j')]
      congr 1
      refine Finset.sum_congr rfl fun j' _ => ?_
      rw [integral_const_mul]
      rfl
    obtain ⟨M₁, hM₁⟩ := h44 e j _ hre1
    choose Mb hMb using fun j' : Fin (nE ē) => h44 ē j' _ hre2
    have hDb : ∀ x ∈ AutomorphicForm.canonicalTruncationDomain K α β, ‖D x‖ ≤ M₁ + ∑ j' : Fin (nE ē), ‖c j'‖ * Mb j' := by
      intro x hx
      have h0 : AutomorphicForm.constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)) (fun u => AutomorphicForm.unipotentGL2 u) D x = 0 := by simpa only [hD] using hCT x
      have hDx : D x = (EE e j ((t : ℂ) * Complex.I) x - AutomorphicForm.constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)) (fun u => AutomorphicForm.unipotentGL2 u) (EE e j ((t : ℂ) * Complex.I)) x) -
          ∑ j' : Fin (nE ē), c j' * (EE ē j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) x - AutomorphicForm.constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)) (fun u => AutomorphicForm.unipotentGL2 u) (EE ē j' (-((((t + σ : ℝ) : ℂ)) * Complex.I))) x) := by
        calc D x = D x - AutomorphicForm.constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)) (fun u => AutomorphicForm.unipotentGL2 u) D x := by rw [h0, sub_zero]
          _ = _ := by
            rw [hCTlin x]
            simp only [hD, mul_sub, Finset.sum_sub_distrib]
            ring
      rw [hDx]
      refine (norm_sub_le _ _).trans (add_le_add (hM₁ x hx) ((norm_sum_le _ _).trans ?_))
      refine Finset.sum_le_sum fun j' _ => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hMb j' x hx) (norm_nonneg _)
    exact MemLp.of_bound S2.aestronglyMeasurable (M₁ + ∑ j' : Fin (nE ē), ‖c j'‖ * Mb j')
      (hmem.mono fun x hx => hDb x hx)

  have hint_orth : ∀ (e₀ : ιE) (j₀ : Fin (nE e₀)) (s₀ : ℂ), s₀.re = 0 → ∀ i : ι,
      Integrable (fun x => EE e₀ j₀ s₀ x * conj (b i x))
        ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := by
    intro e₀ j₀ s₀ hs₀ i
    obtain ⟨M₁, hM₁⟩ := h44 e₀ j₀ s₀ hs₀
    obtain ⟨M₂, A, hM₂⟩ := h00 e₀ j₀ s₀ hs₀
    obtain ⟨C, hC0, hC⟩ :=
      AutomorphicForm.forall_exists_forall_norm_le_mul_inv_adelicHeight_pow_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule
        K α β hα hαβ ξK hξc hξt SK N hN tysK (cls i) (b i) (hb i).2 ⌈max A 0⌉₊
    have hAk : A - (⌈max A 0⌉₊ : ℝ) ≤ 0 := by
      have h1 : max A 0 ≤ (⌈max A 0⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : A ≤ max A 0 := le_max_left _ _
      linarith
    have hbound : ∀ x ∈ AutomorphicForm.canonicalTruncationDomain K α β, ‖EE e₀ j₀ s₀ x * conj (b i x)‖ ≤
        |M₁| * C * h₀⁻¹ ^ ⌈max A 0⌉₊ + |M₂| * C * h₀ ^ (A - (⌈max A 0⌉₊ : ℝ)) := by
      intro x hx
      have hHx : h₀ ≤ NumberField.AdelicHeight.adelicHeight K x := hfloor x hx
      have hHpos : 0 < NumberField.AdelicHeight.adelicHeight K x := NumberField.AdelicHeight.adelicHeight_pos x
      have hE : ‖EE e₀ j₀ s₀ x‖ ≤ |M₁| + |M₂| * (NumberField.AdelicHeight.adelicHeight K x) ^ A := by
        calc ‖EE e₀ j₀ s₀ x‖ = ‖(EE e₀ j₀ s₀ x - AutomorphicForm.constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)) (fun u => AutomorphicForm.unipotentGL2 u) (EE e₀ j₀ s₀) x) + AutomorphicForm.constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)) (fun u => AutomorphicForm.unipotentGL2 u) (EE e₀ j₀ s₀) x‖ := by
              rw [sub_add_cancel]
          _ ≤ ‖EE e₀ j₀ s₀ x - AutomorphicForm.constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)) (fun u => AutomorphicForm.unipotentGL2 u) (EE e₀ j₀ s₀) x‖ + ‖AutomorphicForm.constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)) (fun u => AutomorphicForm.unipotentGL2 u) (EE e₀ j₀ s₀) x‖ := norm_add_le _ _
          _ ≤ |M₁| + |M₂| * (NumberField.AdelicHeight.adelicHeight K x) ^ A :=
              add_le_add ((hM₁ x hx).trans (le_abs_self _))
                ((hM₂ x hx).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hHpos.le _)))
      have hbx : ‖b i x‖ ≤ C * (NumberField.AdelicHeight.adelicHeight K x)⁻¹ ^ ⌈max A 0⌉₊ := hC x (hΦs hx)
      have hpow : (NumberField.AdelicHeight.adelicHeight K x)⁻¹ ^ ⌈max A 0⌉₊ ≤ h₀⁻¹ ^ ⌈max A 0⌉₊ :=
        pow_le_pow_left₀ (inv_nonneg.mpr hHpos.le) (inv_anti₀ h₀pos hHx) _
      have hrp : (NumberField.AdelicHeight.adelicHeight K x) ^ A * (NumberField.AdelicHeight.adelicHeight K x)⁻¹ ^ ⌈max A 0⌉₊ ≤ h₀ ^ (A - (⌈max A 0⌉₊ : ℝ)) := by
        have : (NumberField.AdelicHeight.adelicHeight K x) ^ A * (NumberField.AdelicHeight.adelicHeight K x)⁻¹ ^ ⌈max A 0⌉₊ = (NumberField.AdelicHeight.adelicHeight K x) ^ (A - (⌈max A 0⌉₊ : ℝ)) := by
          rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg hHpos.le, ← Real.rpow_add hHpos, sub_eq_add_neg]
        rw [this]
        exact Real.rpow_le_rpow_of_nonpos h₀pos hHx hAk
      calc ‖EE e₀ j₀ s₀ x * conj (b i x)‖ = ‖EE e₀ j₀ s₀ x‖ * ‖b i x‖ := by
            rw [norm_mul, Complex.norm_conj]
        _ ≤ (|M₁| + |M₂| * (NumberField.AdelicHeight.adelicHeight K x) ^ A) * (C * (NumberField.AdelicHeight.adelicHeight K x)⁻¹ ^ ⌈max A 0⌉₊) :=
            mul_le_mul hE hbx (norm_nonneg _) (by positivity)
        _ = |M₁| * C * (NumberField.AdelicHeight.adelicHeight K x)⁻¹ ^ ⌈max A 0⌉₊ +
              |M₂| * C * ((NumberField.AdelicHeight.adelicHeight K x) ^ A * (NumberField.AdelicHeight.adelicHeight K x)⁻¹ ^ ⌈max A 0⌉₊) := by ring
        _ ≤ |M₁| * C * h₀⁻¹ ^ ⌈max A 0⌉₊ + |M₂| * C * h₀ ^ (A - (⌈max A 0⌉₊ : ℝ)) :=
            add_le_add (mul_le_mul_of_nonneg_left hpow (by positivity))
              (mul_le_mul_of_nonneg_left hrp (by positivity))
    have hmeas : AEStronglyMeasurable (fun x => EE e₀ j₀ s₀ x * conj (b i x)) ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) :=
      ((hcontE e₀ j₀ s₀ hs₀).mul (Complex.continuous_conj.comp (hbcont i))).aestronglyMeasurable
    exact memLp_one_iff_integrable.mp (MemLp.of_bound hmeas _ (hmem.mono fun x hx => hbound x hx))
  have hORTH : ∀ (e₀ : ιE) (j₀ : Fin (nE e₀)) (s₀ : ℂ), s₀.re = 0 → ∀ i : ι,
      ∫ x in AutomorphicForm.canonicalTruncationDomain K α β, EE e₀ j₀ s₀ x * conj (b i x) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 :=
    fun e₀ j₀ s₀ hs₀ i =>
      AutomorphicForm.setIntegral_axis_continuation_mul_conj_cuspBasis_eq_zero_of_mem K α β hα hαβ ΦK cK uK d₁K d₂K TK
        hcK hd₁K hdK hcovK νZK ΩK hΩK SK ξK hξc hξt N hN tysK hξu hαm ι b cls hb hbn hbo hbs hbc ιE μ ν hμ hν hμic hνic
        hμc hνc hμν hdist nE φE hφE hφEK hφEf hφEjc hφEhol hφEKu hφEflat hφElev hφEty hφEon hφEspan hpairs OE EE NE hEE
        e₀ j₀ s₀ ((hEE e₀ j₀).2.2.1 hs₀) i
  have S7 : ∀ i, ∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
      D x * conj (b i x) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 := by
    intro i
    have hre1 : (((t : ℂ) * Complex.I)).re = 0 := by simp
    have hre2 : ((-((((t + σ : ℝ) : ℂ)) * Complex.I))).re = 0 := by simp
    have h1 := hint_orth e j ((t : ℂ) * Complex.I) hre1 i
    have h2 : ∀ j' : Fin (nE ē), Integrable (fun x => c j' * EE ē j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) x * conj (b i x))
        ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := by
      intro j'
      have := (hint_orth ē j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) hre2 i).const_mul (c j')
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.mul_apply]; ring
    have hexp : (fun x => D x * conj (b i x)) = fun x => EE e j ((t : ℂ) * Complex.I) x * conj (b i x) -
        ∑ j' : Fin (nE ē), c j' * EE ē j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) x * conj (b i x) := by
      funext x; rw [hD]; simp only [Finset.sum_mul, sub_mul]
    rw [hexp, integral_sub h1 (integrable_finset_sum _ (fun j' _ => h2 j')), integral_finset_sum _ (fun j' _ => h2 j'),
      hORTH e j ((t : ℂ) * Complex.I) hre1 i]
    have : ∀ j' : Fin (nE ē), ∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
        c j' * EE ē j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) x * conj (b i x) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 := by
      intro j'
      have h0 := hORTH ē j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) hre2 i
      simp_rw [mul_assoc]
      rw [integral_const_mul, h0, mul_zero]
    rw [Finset.sum_eq_zero (fun j' _ => this j'), sub_zero]

  have Scusp : IsSmoothCuspAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK D := by
    refine ⟨⟨?_, ?_⟩, S5⟩
    · exact (AutomorphicForm.lsXiMemberAt_iff (𝓞 K) K _ _ _ _ D).mpr ⟨S1, S6⟩
    · intro x
      have := hCT x
      simp only [hD] at this
      exact this
  have hae : D =ᵐ[(adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)] 0 :=
    hbc D Scusp S2 S3 S4 S7
  have S9 : ∀ x : AdelicGL2 (𝓞 K) K, D x = 0 := by
    obtain ⟨-, -, -, hΦs, hΦ⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ
    have hae2 : ∀ᵐ p : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K
        ∂(((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)).prod
          ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))),
        (fun x (_ : AdelicGL2 (𝓞 K) K) => D x) p.1 p.2 = 0 :=
      Measure.quasiMeasurePreserving_fst.ae hae
    have h := AutomorphicForm.forall_eq_zero_of_ae_prod_restrict_eq_zero_of_apply_globalPoints_mul_of_apply_centralScalar_mul_of_isFundamentalDomain_slab
      K α β hα hαβ (AutomorphicForm.canonicalTruncationDomain K α β) hΦs hΦ (fun x _ => D x)
      (fun _ => S2) (fun _ => continuous_const) (fun γ x _ => S1.left_invariant γ x) (fun _ _ _ => rfl)
      (fun z x _ h0 => by
        have h0' : D x = 0 := h0
        show D (AutomorphicForm.centralScalar (𝓞 K) K z * x) = 0
        rw [S1.central_transform ⟨z, Subgroup.mem_top z⟩ x, h0', mul_zero])
      (fun _ _ _ h0 => h0) hae2
    exact fun x => h x x
  simpa [hD] using S9 g

end S_AutomorphicForm_forall_axis_continuation_sub_sum_mul_axis_continuation_eq_zero_of_forall_constantTerm_eq_zero
end P2MW
export P2MW.S_AutomorphicForm_forall_axis_continuation_sub_sum_mul_axis_continuation_eq_zero_of_forall_constantTerm_eq_zero (solution)
