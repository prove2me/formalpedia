-- Prove2me | solution 1 for AutomorphicForm.forall_integrableOn_and_setIntegral_lambdaT_mul_tsum_convOp_mul_conj_eq_mul_tsum_cutTrace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/29d9b40c-433f-56be-a9a2-52140093ed0f

import Theorems.Thm_AutomorphicForm_forall_isCompact_exists_tsum_norm_convOp_mul_conj_le_and_summable_setIntegral_norm_finsum_of_orthonormal_principalLevel_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_finsum_setIntegral_convOp_mul_conj_eq_cutTrace_of_orthonormal_principalLevel_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_isotypicCuspSubmodule_le_of_coversModCentre_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_isotypicCuspSubmodule_inf_archCutSubmodule_principalLevel_le_of_isFundamentalDomain_of_pos
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_forall_integrableOn_and_setIntegral_lambdaT_mul_tsum_convOp_mul_conj_eq_mul_tsum_cutTrace
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.CuspidalConstituent.rightRegular_apply AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.iotaZsqrtdNegTwo_apply LanglandsTunnell.Converse.ArchDatumC.mk.injEq LanglandsTunnell.Converse.ArchDatumC.mk.sizeOf_spec LanglandsTunnell.Converse.FinWhittakerDatum.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.injEq LanglandsTunnell.Converse.FinWhittakerDatum.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.sizeOf_spec LanglandsTunnell.Converse.JLData.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.injEq LanglandsTunnell.Converse.JLData.mk.sizeOf_spec AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq"
p2m_attr_erase "simp" "M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply HeckePair.IsGelfandInvolution.reindex_mk HeckePair.IsGelfandInvolution.reindexInv_mk"

set_option autoImplicit false
set_option linter.deprecated false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate ENNReal NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace R1CuspBlock

open Filter Topology AutomorphicForm

section General

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem integrable_tsum_of_summable_integral_norm {ι : Type*} [Countable ι] {F : ι → X → ℂ}
    (hF : ∀ i, Integrable (F i) μ) (hs : Summable fun i => ∫ a, ‖F i a‖ ∂μ) :
    Integrable (fun a => ∑' i, F i a) μ := by
  have hmeas : ∀ i, AEStronglyMeasurable (F i) μ := fun i => (hF i).1
  have hlin : ∀ i, ∫⁻ a, ‖F i a‖ₑ ∂μ = ENNReal.ofReal (∫ a, ‖F i a‖ ∂μ) := fun i => by
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hF i)]
  have htsum : ∑' i, ∫⁻ a, ‖F i a‖ₑ ∂μ ≠ ⊤ := by
    simp_rw [hlin]
    exact hs.tsum_ofReal_ne_top
  have hae : ∀ᵐ a ∂μ, Summable fun i => ‖F i a‖ := by
    have h1 : ∫⁻ a, ∑' i, ‖F i a‖ₑ ∂μ ≠ ⊤ := by
      rwa [lintegral_tsum fun i => (hmeas i).enorm]
    have h2 := ae_lt_top' (AEMeasurable.ennreal_tsum fun i => (hmeas i).enorm) h1
    filter_upwards [h2] with a ha
    have h3 : ∑' i, (‖F i a‖₊ : ℝ≥0∞) ≠ ⊤ := by simpa [enorm_eq_nnnorm] using ha.ne
    simpa only [coe_nnnorm] using ENNReal.tsum_coe_ne_top_iff_summable_coe.mp h3
  have hlim : ∀ᵐ a ∂μ, Tendsto (fun s : Finset ι => ∑ i ∈ s, F i a) atTop (𝓝 (∑' i, F i a)) := by
    filter_upwards [hae] with a ha
    exact ha.of_norm.hasSum
  have hsm : AEStronglyMeasurable (fun a => ∑' i, F i a) μ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun s => Finset.aestronglyMeasurable_fun_sum s fun i _ => hmeas i) hlim
  refine ⟨hsm, ?_⟩
  have hbound : ∀ᵐ a ∂μ, ‖∑' i, F i a‖ₑ ≤ ∑' i, ‖F i a‖ₑ := by
    filter_upwards [hae] with a ha
    exact enorm_tsum_le_tsum_enorm
  show ∫⁻ a, ‖∑' i, F i a‖ₑ ∂μ < ⊤
  calc ∫⁻ a, ‖∑' i, F i a‖ₑ ∂μ ≤ ∫⁻ a, ∑' i, ‖F i a‖ₑ ∂μ := lintegral_mono_ae hbound
    _ = ∑' i, ∫⁻ a, ‖F i a‖ₑ ∂μ := lintegral_tsum fun i => (hmeas i).enorm
    _ < ⊤ := htsum.lt_top

theorem countable_of_orthonormal [IsSeparable μ] {ι : Type*} (b : ι → X → ℂ)
    (hbm : ∀ i, AEStronglyMeasurable (b i) μ)
    (hb₁ : ∀ i, ∫ x, b i x * conj (b i x) ∂μ = 1)
    (hb₀ : ∀ i j, i ≠ j → ∫ x, b i x * conj (b j x) ∂μ = 0) : Countable ι := by
  classical
  haveI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.ofNat_ne_top⟩

  have hint : ∀ i, Integrable (fun x => b i x * conj (b i x)) μ := by
    intro i
    by_contra h
    have h1 := hb₁ i
    rw [integral_undef h] at h1
    exact zero_ne_one h1
  have hL2 : ∀ i, MemLp (b i) 2 μ := by
    intro i
    refine (memLp_two_iff_integrable_sq_norm (hbm i)).2 ((hint i).norm.congr ?_)
    filter_upwards with x
    rw [norm_mul, RCLike.norm_conj, sq]

  set v : ι → Lp ℂ 2 μ := fun i => (hL2 i).toLp with hv
  have hinner : ∀ i j, inner ℂ (v i) (v j) = conj (∫ x, b i x * conj (b j x) ∂μ) := by
    intro i j
    rw [L2.inner_def, ← integral_conj]
    refine integral_congr_ae ?_
    filter_upwards [(hL2 i).coeFn_toLp, (hL2 j).coeFn_toLp] with x hx hy
    simp only [hv, hx, hy, RCLike.inner_apply, map_mul, RCLike.conj_conj, mul_comm]
  have horth : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [hinner]
    split_ifs with h
    · subst h; rw [hb₁, map_one]
    · rw [hb₀ i j h, map_zero]

  have hdist : ∀ i j, i ≠ j → (1 : ℝ) ≤ ‖v i - v j‖ := by
    intro i j hij
    have h2 : ‖v i - v j‖ ^ 2 = 2 := by
      rw [@norm_sub_sq ℂ, horth.1 i, horth.1 j, (orthonormal_iff_ite.1 horth) i j, if_neg hij]
      simp
      norm_num
    nlinarith [norm_nonneg (v i - v j)]

  have hpd : (Set.univ : Set ι).PairwiseDisjoint fun i => Metric.ball (v i) (1 / 2) := by
    intro i _ j _ hij
    refine Set.disjoint_left.2 fun z hzi hzj => ?_
    have h1 := hdist i j hij
    have h2 : dist (v i) (v j) < 1 := by
      calc dist (v i) (v j) ≤ dist (v i) z + dist z (v j) := dist_triangle _ _ _
        _ < 1 / 2 + 1 / 2 := add_lt_add (by rw [dist_comm]; exact hzi) hzj
        _ = 1 := by norm_num
    rw [dist_eq_norm] at h2
    linarith
  have hcnt : (Set.univ : Set ι).Countable :=
    hpd.countable_of_isOpen (fun i _ => Metric.isOpen_ball)
      (fun i _ => ⟨v i, Metric.mem_ball_self (by norm_num)⟩)
  exact Set.countable_univ_iff.1 hcnt

end General

private theorem _root_.R1CuspBlock.exists_notMem_finset (K : Type) [Field K] [NumberField K] (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ v : HeightOneSpectrum (𝓞 K), v ∉ T := by
  have hinj : ∀ p : Nat.Primes, ∃ v : HeightOneSpectrum (𝓞 K), v.asIdeal.under ℤ = Ideal.span {(p.1 : ℤ)} := by
    intro p
    haveI hpr : (Ideal.span {(p.1 : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime (by exact_mod_cast p.2.ne_zero)).mpr (Nat.prime_iff_prime_int.mp p.2)
    have hp0 : Ideal.span {(p.1 : ℤ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast p.2.ne_zero
    obtain ⟨⟨Q, hQ⟩⟩ := (inferInstance : Nonempty ((Ideal.span {(p.1 : ℤ)}).primesOver (𝓞 K)))
    exact ⟨⟨Q, hQ.1, Ideal.ne_bot_of_mem_primesOver hp0 hQ⟩, hQ.2.over.symm⟩
  choose g hg using hinj
  have hginj : Function.Injective g := by
    intro p q hpq
    have h := hg p
    rw [hpq, hg q] at h
    have h' := Int.associated_iff_natAbs.mp (Ideal.span_singleton_eq_span_singleton.mp h)
    simp only [Int.natAbs_natCast] at h'
    exact Subtype.ext h'.symm
  haveI : Infinite (HeightOneSpectrum (𝓞 K)) := Infinite.of_injective g hginj
  exact Infinite.exists_notMem_finset T

p2m_export "R1CuspBlock" "exists_notMem_finset"

theorem level_ne_bot (K : Type) [Field K] [NumberField K] (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hNS : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ S) : N ≠ ⊥ := by
  rintro rfl
  obtain ⟨v, hv⟩ := exists_notMem_finset K S
  exact hv (hNS v (dvd_zero _))

section Adelic

attribute [local instance] NumberField.AdelicHaar.adeleBorel

variable (K : Type) [Field K] [NumberField K]

abbrev P (D : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)) : AutomorphicForm.CarrierPins K :=
  AutomorphicForm.productionPinsOf K D (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
    (fun v => heckeGen (𝓞 K) K v) (adelicBox K)

abbrev boxMeasure : Measure (AdeleRing (𝓞 K) K) :=
  ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)

theorem integrable_comp_unipotent {φ : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ} (hφ : Continuous φ)
    (g : AutomorphicForm.AdelicGL2 (𝓞 K) K) :
    Integrable (fun q : AdeleRing (𝓞 K) K => φ (AutomorphicForm.unipotentGL2 q * g)) (boxMeasure K) := by
  haveI : BorelSpace (AdeleRing (𝓞 K) K) := borelSpace_adeleBorel (𝓞 K) K
  haveI : IsProbabilityMeasure (boxMeasure K) := isProbabilityMeasure_cond_adelicBox K
  have hc : Continuous fun q : AdeleRing (𝓞 K) K => φ (AutomorphicForm.unipotentGL2 q * g) :=
    hφ.comp ((AutomorphicForm.continuous_unipotentGL2).mul continuous_const)
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_adelicBox_subset K
  obtain ⟨M, hM⟩ := (hC.image hc).isBounded.exists_norm_le
  refine Integrable.of_bound hc.aestronglyMeasurable M ?_
  filter_upwards [ProbabilityTheory.ae_cond_mem (μ := adelicAddHaar (𝓞 K) K) (measurableSet_adelicBox K)]
    with q hq
  exact hM _ ⟨q, hsub hq, rfl⟩

theorem constantTerm_eq_zero_of_mem (D : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (N : Ideal (𝓞 K))
    (S : Finset (HeightOneSpectrum (𝓞 K))) (π : HeckeEigensystem K ℂ)
    {φ : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : φ ∈ AutomorphicForm.isotypicCuspSubmodule K (P K D) ξ N S π)
    (g : AutomorphicForm.AdelicGL2 (𝓞 K) K) :
    AutomorphicForm.constantTerm (boxMeasure K) (fun t => AutomorphicForm.unipotentGL2 t) φ g = 0 := by
  revert g
  refine Submodule.span_induction
    (p := fun φ _ => Continuous φ ∧ ∀ g,
      AutomorphicForm.constantTerm (boxMeasure K) (fun t => AutomorphicForm.unipotentGL2 t) φ g = 0)
    ?_ ?_ ?_ ?_ hφ |>.2
  · intro φ hφ
    exact ⟨hφ.continuous, fun g => hφ.smoothCusp.1.2 g⟩
  · exact ⟨continuous_zero, fun g => AutomorphicForm.constantTerm_zero _ _ g⟩
  · rintro φ ψ - - ⟨hφc, hφ0⟩ ⟨hψc, hψ0⟩
    refine ⟨hφc.add hψc, fun g => ?_⟩
    have h := integral_add (integrable_comp_unipotent K hφc g) (integrable_comp_unipotent K hψc g)
    unfold AutomorphicForm.constantTerm AutomorphicForm.constantTermIntegrand at hφ0 hψ0 ⊢
    simp only [Pi.add_apply]
    rw [h, hφ0 g, hψ0 g, add_zero]
  · rintro c φ - ⟨hφc, hφ0⟩
    refine ⟨hφc.const_smul c, fun g => ?_⟩
    unfold AutomorphicForm.constantTerm AutomorphicForm.constantTermIntegrand at hφ0 ⊢
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul, hφ0 g, mul_zero]

theorem constantTerm_tsum_eq_zero {ι : Type} [Countable ι] (D : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (N : Ideal (𝓞 K))
    (S : Finset (HeightOneSpectrum (𝓞 K))) (cls : ι → HeckeEigensystem K ℂ)
    (b : ι → AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ)
    (hbV : ∀ i, b i ∈ AutomorphicForm.isotypicCuspSubmodule K (P K D) ξ N S (cls i))
    (c : ι → ℂ) (a : ℂ)
    (hbd : ∀ C : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K), IsCompact C → ∃ M : ℝ, ∀ y ∈ C,
      Summable (fun i => ‖c i * conj (b i y)‖) ∧ ∑' i, ‖c i * conj (b i y)‖ ≤ M)
    (g : AutomorphicForm.AdelicGL2 (𝓞 K) K) :
    AutomorphicForm.constantTerm (boxMeasure K) (fun t => AutomorphicForm.unipotentGL2 t)
      (fun y => a * ∑' i, c i * conj (b i y)) g = 0 := by
  haveI : BorelSpace (AdeleRing (𝓞 K) K) := borelSpace_adeleBorel (𝓞 K) K
  haveI : IsProbabilityMeasure (boxMeasure K) := isProbabilityMeasure_cond_adelicBox K
  have hbc : ∀ i, Continuous (b i) := fun i =>
    AutomorphicForm.continuous_of_mem_isotypicCuspSubmodule (hbV i)

  obtain ⟨Cb, hCb, hsub⟩ := exists_isCompact_adelicBox_subset K
  have hn : Continuous fun q : AdeleRing (𝓞 K) K => AutomorphicForm.unipotentGL2 q * g :=
    (AutomorphicForm.continuous_unipotentGL2).mul continuous_const
  obtain ⟨M, hM⟩ := hbd _ (hCb.image hn)

  set G : ι → AdeleRing (𝓞 K) K → ℂ := fun i q => c i * conj (b i (AutomorphicForm.unipotentGL2 q * g))
    with hG
  have hGm : ∀ i, AEStronglyMeasurable (G i) (boxMeasure K) := fun i =>
    (continuous_const.mul (Complex.continuous_conj.comp ((hbc i).comp hn))).aestronglyMeasurable
  have hGb : ∀ᵐ q ∂(boxMeasure K), (∑' i, ‖G i q‖ₑ) ≤ ENNReal.ofReal M := by
    filter_upwards [ProbabilityTheory.ae_cond_mem (μ := adelicAddHaar (𝓞 K) K) (measurableSet_adelicBox K)]
      with q hq
    obtain ⟨hs, hle⟩ := hM _ ⟨q, hsub hq, rfl⟩
    have hs' : Summable fun i => ‖G i q‖ := hs
    have hle' : ∑' i, ‖G i q‖ ≤ M := hle
    have h1 : (∑' i, ‖G i q‖ₑ) = ENNReal.ofReal (∑' i, ‖G i q‖) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun i => norm_nonneg _) hs']
      exact tsum_congr fun i => (ofReal_norm_eq_enorm (G i q)).symm
    rw [h1]
    exact ENNReal.ofReal_le_ofReal hle'
  have hGsum : ∑' i, ∫⁻ q, ‖G i q‖ₑ ∂(boxMeasure K) ≠ ⊤ := by
    rw [← lintegral_tsum fun i => (hGm i).enorm]
    refine ne_top_of_le_ne_top (b := ∫⁻ _, ENNReal.ofReal M ∂(boxMeasure K)) ?_ (lintegral_mono_ae hGb)
    rw [lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)

  have hGi : ∀ i, ∫ q, G i q ∂(boxMeasure K) = 0 := by
    intro i
    have h0 : ∫ q, b i (AutomorphicForm.unipotentGL2 q * g) ∂(boxMeasure K) = 0 :=
      constantTerm_eq_zero_of_mem K D ξ N S (cls i) (hbV i) g
    show ∫ q, c i * conj (b i (AutomorphicForm.unipotentGL2 q * g)) ∂(boxMeasure K) = 0
    rw [integral_const_mul, integral_conj, h0, map_zero, mul_zero]
  have h : ∫ q, ∑' i, G i q ∂(boxMeasure K) = 0 := by
    rw [integral_tsum hGm hGsum]
    simp [hGi]
  show ∫ q, a * ∑' i, c i * conj (b i (AutomorphicForm.unipotentGL2 q * g)) ∂(boxMeasure K) = 0
  rw [integral_const_mul]
  have h' : ∫ q, ∑' i, c i * conj (b i (AutomorphicForm.unipotentGL2 q * g)) ∂(boxMeasure K) = 0 := h
  rw [h', mul_zero]

end Adelic

theorem convTraceOn_congr (K : Type) [Field K] [NumberField K]
    {V₁ V₂ : Submodule ℂ (AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ)} (h : V₁ = V₂)
    (h₁ : ∀ u ∈ V₁, Continuous u) (h₂ : ∀ u ∈ V₂, Continuous u)
    (f : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    AutomorphicForm.convTraceOn K V₁ h₁ f hf hfc = AutomorphicForm.convTraceOn K V₂ h₂ f hf hfc := by
  subst h
  rfl

theorem tsum_eq_tsum_finsum_fibre {ι : Type} {Y : Type} (cls : ι → Y) (I : ι → ℂ)
    (hI : Summable fun i => ‖I i‖) (hfin : ∀ y : Y, Finite {i // cls i = y}) :
    ∑' i, I i = ∑' y : Y, ∑ᶠ c : {i // cls i = y}, I c.1 := by
  set e : (Σ y : Y, {i // cls i = y}) ≃ ι := Equiv.sigmaFiberEquiv cls with he
  have h1 : ∑' i, I i = ∑' p : (Σ y : Y, {i // cls i = y}), I (e p) := (Equiv.tsum_eq e I).symm
  rw [h1]
  have hs : Summable fun p : (Σ y : Y, {i // cls i = y}) => I (e p) :=
    (e.summable_iff (f := I)).2 hI.of_norm
  have hfib : ∀ y : Y, Summable fun c : {i // cls i = y} => I (e ⟨y, c⟩) := by
    intro y
    haveI := hfin y
    exact Summable.of_finite
  rw [Summable.tsum_sigma' hfib hs]
  refine tsum_congr fun y => ?_
  haveI := hfin y
  rw [tsum_eq_finsum (Set.toFinite _)]
  rfl

section Main

attribute [local instance] NumberField.AdelicHaar.adeleBorel

variable (K : Type) [Field K] [NumberField K]

theorem main
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (ι : Type) (b : ι → AdelicGL2 (𝓞 K) K → ℂ) (cls : ι → HeckeEigensystem K ℂ)
    (hb : ∀ i, cls i ∈ cuspClasses K (P K (canonicalTruncationDomain K α β)) ξK N SK ∧
        b i ∈ isotypicCuspSubmodule K (P K (canonicalTruncationDomain K α β)) ξK N SK (cls i) ⊓
          archCutSubmodule K tysK)
    (hbn : ∀ i, ∫ g in canonicalTruncationDomain K α β,
        b i g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 1)
    (hbo : ∀ i j, i ≠ j → ∫ g in canonicalTruncationDomain K α β,
        b i g * conj (b j g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
    (hbs : ∀ π ∈ cuspClasses K (P K (canonicalTruncationDomain K α β)) ξK N SK,
        {i | cls i = π}.Finite ∧
        Submodule.span ℂ (b '' {i | cls i = π}) =
          isotypicCuspSubmodule K (P K (canonicalTruncationDomain K α β)) ξK N SK π ⊓
            archCutSubmodule K tysK)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hff : IsFactorizableTestFn K f)
    (hbi : IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f)
    (hfin : IsArchBiFinite K tysK f) (R : ℝ) (B : ℂ) :
    IntegrableOn (fun x =>
        lambdaT (P K ΦK).ν (fun t => unipotentGL2 t) (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
          (fun y' => B * ∑' i : ι, convOp K f (b i) x * conj (b i y')) x)
      (canonicalTruncationDomain K α β) (adelicGLHaar (Fin 2) (𝓞 K) K) ∧
    ∫ x in canonicalTruncationDomain K α β,
        lambdaT (P K ΦK).ν (fun t => unipotentGL2 t) (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
          (fun y' => B * ∑' i : ι, convOp K f (b i) x * conj (b i y')) x
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      B * ∑' π : {π : HeckeEigensystem K ℂ //
          π ∈ cuspClasses K (P K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)) ξK N SK},
        cutTrace K (P K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)) ξK N SK π.1 tysK
          f hf hfc := by
  classical

  set μ : Measure (AdelicGL2 (𝓞 K) K) := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  set Φ₀ : Set (AdelicGL2 (𝓞 K) K) := canonicalTruncationDomain K α β with hΦ₀
  set W : Set (AdelicGL2 (𝓞 K) K) := ⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K with hW
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  haveI : μ.IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI : SigmaFinite μ := inferInstance
  haveI : MeasurableSpace.CountablyGenerated (AdelicGL2 (𝓞 K) K) := inferInstance
  haveI : IsSeparable (μ.restrict Φ₀) := inferInstance
  have hN0 : N ≠ ⊥ := level_ne_bot K N SK hN
  obtain ⟨-, -, -, hΦ₀s, hΦ₀fd⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ
  have hbc : ∀ i, Continuous (b i) := fun i =>
    continuous_of_mem_isotypicCuspSubmodule (Submodule.mem_inf.mp (hb i).2).1
  have hbV : ∀ i, b i ∈ isotypicCuspSubmodule K (P K Φ₀) ξK N SK (cls i) := fun i =>
    (Submodule.mem_inf.mp (hb i).2).1

  haveI : Countable ι :=
    countable_of_orthonormal (μ := μ.restrict Φ₀) b (fun i => (hbc i).aestronglyMeasurable) hbn hbo

  obtain ⟨hK1, hKint, hK2⟩ :=
    AutomorphicForm.forall_isCompact_exists_tsum_norm_convOp_mul_conj_le_and_summable_setIntegral_norm_finsum_of_orthonormal_principalLevel_of_isFundamentalDomain_slab
      K α β hα hαβ Φ₀ hΦ₀s hΦ₀fd ξK SK N hN tysK ι b cls hb hbn hbo hbs f hf hfc hff hbi hfin

  set F : ι → AdelicGL2 (𝓞 K) K → ℂ := fun i x => convOp K f (b i) x * conj (b i x) with hF
  have hct : ∀ x : AdelicGL2 (𝓞 K) K,
      constantTerm (P K ΦK).ν (fun t => unipotentGL2 t)
        (fun y' => B * ∑' i : ι, convOp K f (b i) x * conj (b i y')) x = 0 := by
    intro x
    refine constantTerm_tsum_eq_zero K Φ₀ ξK N SK cls b hbV (fun i => convOp K f (b i) x) B ?_ x
    intro C hC
    obtain ⟨M, hM⟩ := hK1 (insert x C) (hC.insert x)
    exact ⟨M, fun y hy => hM x (Set.mem_insert _ _) y (Set.mem_insert_of_mem _ hy)⟩
  have hLAM : (fun x => lambdaT (P K ΦK).ν (fun t => unipotentGL2 t) (NumberField.AdelicHeight.adelicHeight K)
        (Real.exp R) (fun y' => B * ∑' i : ι, convOp K f (b i) x * conj (b i y')) x) =
      fun x => B * ∑' i, F i x := by
    funext x
    rw [lambdaT_apply, Set.indicator_apply]
    split_ifs with h
    · rw [hct x, sub_zero]
    · rw [sub_zero]
  rw [hLAM]

  have hfibre : ∀ π : HeckeEigensystem K ℂ, Finite {i // cls i = π} := by
    intro π
    by_cases hπ : π ∈ cuspClasses K (P K Φ₀) ξK N SK
    · exact ((hbs π hπ).1).to_subtype
    · haveI : IsEmpty {i // cls i = π} := ⟨fun c => hπ (c.2 ▸ (hb c.1).1)⟩
      infer_instance
  set G : HeckeEigensystem K ℂ → AdelicGL2 (𝓞 K) K → ℂ :=
    fun π x => ∑ᶠ c : {i // cls i = π}, F c.1 x with hG
  have hGint : ∀ π : HeckeEigensystem K ℂ, Integrable (G π) (μ.restrict Φ₀) := by
    intro π
    haveI := hfibre π
    haveI : Fintype {i // cls i = π} := Fintype.ofFinite _
    have hGπ : G π = fun x => ∑ c : {i // cls i = π}, F c.1 x := by
      funext x; simp only [hG, finsum_eq_sum_of_fintype]
    rw [hGπ]
    exact integrable_finset_sum _ fun c _ => hKint c.1

  have hpt : ∀ x, ∑' i, F i x = ∑' π : HeckeEigensystem K ℂ, G π x := by
    intro x
    obtain ⟨M, hM⟩ := hK1 {x} isCompact_singleton
    have hs : Summable fun i => ‖F i x‖ := (hM x (Set.mem_singleton x) x (Set.mem_singleton x)).1
    have := tsum_eq_tsum_finsum_fibre cls (fun i => F i x) hs hfibre
    simpa only [hG] using this

  haveI : Countable ↥(Set.range cls) := (Set.countable_range cls).to_subtype
  have hGzero : ∀ π : HeckeEigensystem K ℂ, π ∉ Set.range cls → G π = 0 := by
    intro π hπ
    haveI : IsEmpty {i // cls i = π} := ⟨fun c => hπ ⟨c.1, c.2⟩⟩
    funext x
    simp only [hG, finsum_of_isEmpty, Pi.zero_apply]
  have hrange : ∀ x, ∑' π : HeckeEigensystem K ℂ, G π x = ∑' π : ↥(Set.range cls), G π.1 x := by
    intro x
    symm
    refine tsum_subtype_eq_of_support_subset (f := fun π : HeckeEigensystem K ℂ => G π x)
      (s := Set.range cls) ?_
    intro π hπ
    by_contra h
    exact hπ (by simp only [hGzero π h, Pi.zero_apply])
  have hK2r : Summable fun π : ↥(Set.range cls) => ∫ x, ‖G π.1 x‖ ∂(μ.restrict Φ₀) := by
    have h0 : Summable fun π : HeckeEigensystem K ℂ => ∫ x, ‖G π x‖ ∂(μ.restrict Φ₀) := by
      simpa only [hG, hF] using hK2
    exact h0.subtype _
  have hInt : Integrable (fun x => ∑' i, F i x) (μ.restrict Φ₀) := by
    have hI' := integrable_tsum_of_summable_integral_norm (fun π : ↥(Set.range cls) => hGint π.1) hK2r
    refine hI'.congr ?_
    filter_upwards with x
    rw [hpt x, hrange x]
  refine ⟨hInt.const_mul B, ?_⟩
  rw [integral_const_mul]
  congr 1

  set I : ι → ℂ := fun i => ∫ x in Φ₀, F i x ∂μ with hI
  have hstep : ∫ x in Φ₀, ∑' i, F i x ∂μ =
      ∑' π : HeckeEigensystem K ℂ, ∑ᶠ c : {i // cls i = π}, I c.1 := by
    have h1 : ∫ x in Φ₀, ∑' i, F i x ∂μ = ∫ x in Φ₀, ∑' π : ↥(Set.range cls), G π.1 x ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards with x
      rw [hpt x, hrange x]
    have h2 : ∫ x in Φ₀, ∑' π : ↥(Set.range cls), G π.1 x ∂μ =
        ∑' π : ↥(Set.range cls), ∫ x in Φ₀, G π.1 x ∂μ :=
      (integral_tsum_of_summable_integral_norm (fun π : ↥(Set.range cls) => hGint π.1) hK2r).symm
    have h3 : ∀ π : HeckeEigensystem K ℂ, ∫ x in Φ₀, G π x ∂μ = ∑ᶠ c : {i // cls i = π}, I c.1 := by
      intro π
      haveI := hfibre π
      haveI : Fintype {i // cls i = π} := Fintype.ofFinite _
      simp only [hG, hI, finsum_eq_sum_of_fintype]
      exact integral_finset_sum _ fun c _ => hKint c.1
    have h4 : ∑' π : ↥(Set.range cls), ∫ x in Φ₀, G π.1 x ∂μ =
        ∑' π : HeckeEigensystem K ℂ, ∫ x in Φ₀, G π x ∂μ :=
      tsum_subtype_eq_of_support_subset (s := Set.range cls)
        (f := fun π : HeckeEigensystem K ℂ => ∫ x in Φ₀, G π x ∂μ) (by
          intro π hπ
          by_contra h
          exact hπ (by simp only [hGzero π h, Pi.zero_apply, integral_zero]))
    rw [h1, h2, h4]
    exact tsum_congr h3
  rw [hstep]

  have hVle : ∀ π : HeckeEigensystem K ℂ,
      isotypicCuspSubmodule K (P K W) ξK N SK π ≤ isotypicCuspSubmodule K (P K Φ₀) ξK N SK π := fun π =>
    AutomorphicForm.isotypicCuspSubmodule_le_of_coversModCentre_of_isFundamentalDomain_slab K cK uK d₁K d₂K
      TK hdK hcovK α β hα Φ₀ hΦ₀s hΦ₀fd
      (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
      (adelicBox K) ξK N SK π
  have hWeq : ∀ π : HeckeEigensystem K ℂ,
      isotypicCuspSubmodule K (P K W) ξK N SK π ⊓ archCutSubmodule K tysK =
      isotypicCuspSubmodule K (P K Φ₀) ξK N SK π ⊓ archCutSubmodule K tysK := fun π =>
    le_antisymm (inf_le_inf_right _ (hVle π))
      (AutomorphicForm.isotypicCuspSubmodule_inf_archCutSubmodule_principalLevel_le_of_isFundamentalDomain_of_pos
        K α β hα hαβ Φ₀ hΦ₀fd ξK N hN0 SK tysK π cK uK d₁K d₂K TK hcK hd₁K)
  have hcls : ∀ π : HeckeEigensystem K ℂ,
      π ∈ cuspClasses K (P K W) ξK N SK → π ∈ cuspClasses K (P K Φ₀) ξK N SK := by
    rintro π ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun hbot => h3 (le_bot_iff.mp (hbot ▸ hVle π))⟩

  have hJ0 : ∀ π : HeckeEigensystem K ℂ, π ∈ cuspClasses K (P K Φ₀) ξK N SK →
      ∑ᶠ c : {i // cls i = π}, I c.1 = cutTrace K (P K Φ₀) ξK N SK π tysK f hf hfc := fun π hπ =>
    AutomorphicForm.finsum_setIntegral_convOp_mul_conj_eq_cutTrace_of_orthonormal_principalLevel_of_isFundamentalDomain_slab
      K α β hα hαβ Φ₀ hΦ₀s hΦ₀fd Φ₀ hΦ₀s hΦ₀fd ξK SK N hN tysK ι b cls hb hbn hbo hbs f hf hfc hbi hfin π hπ
  have hJ : ∀ π : HeckeEigensystem K ℂ,
      ∑ᶠ c : {i // cls i = π}, I c.1 =
        (cuspClasses K (P K W) ξK N SK).indicator
          (fun π => cutTrace K (P K W) ξK N SK π tysK f hf hfc) π := by
    intro π
    by_cases hπW : π ∈ cuspClasses K (P K W) ξK N SK
    · rw [Set.indicator_of_mem hπW, hJ0 π (hcls π hπW), cutTrace_eq, cutTrace_eq]
      exact (convTraceOn_congr K (hWeq π) _ _ f hf hfc).symm
    rw [Set.indicator_of_notMem hπW]
    by_cases hπ0 : π ∈ cuspClasses K (P K Φ₀) ξK N SK
    · rw [hJ0 π hπ0]

      have hVbot : isotypicCuspSubmodule K (P K W) ξK N SK π = ⊥ := by
        by_contra hne
        exact hπW ⟨hπ0.1, hπ0.2.1, hne⟩
      have hWbot : isotypicCuspSubmodule K (P K Φ₀) ξK N SK π ⊓ archCutSubmodule K tysK = ⊥ := by
        rw [← hWeq π, hVbot, bot_inf_eq]
      by_contra hne
      exact (mapsTo_and_ne_bot_of_cutTrace_ne_zero K hne).2 hWbot
    · haveI : IsEmpty {i // cls i = π} := ⟨fun c => hπ0 (c.2 ▸ (hb c.1).1)⟩
      exact finsum_of_isEmpty _
  rw [tsum_congr hJ, ← tsum_subtype]

end Main

end R1CuspBlock

end

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
        φ =ᵐ[(adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)] 0) :
    ∀ (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f),
      IsFactorizableTestFn K f →
      IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f →
      IsArchBiFinite K tysK f →
      ∀ R : ℝ,
        IntegrableOn (fun x =>
              (@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (fun y' => ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) *
                  ∑' i : ι, convOp K f (b i) x * conj (b i y'))
                x))
          (AutomorphicForm.canonicalTruncationDomain K α β) (adelicGLHaar (Fin 2) (𝓞 K) K) ∧
        ∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
              (@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (fun y' => ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) *
                  ∑' i : ι, convOp K f (b i) x * conj (b i y'))
                x)
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
          ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) *
          ∑' π : {π : HeckeEigensystem K ℂ //
              π ∈ cuspClasses K
                (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
                  (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N SK},
            cutTrace K
              (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
                (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N SK π.1 tysK f hf hfc := by
  intro f hf hfc hff hbi hfin R
  exact R1CuspBlock.main K α β hα hαβ ΦK cK uK d₁K d₂K TK hcK hd₁K hdK hcovK SK ξK N hN tysK ι b cls hb hbn
    hbo hbs f hf hfc hff hbi hfin R _

end S_AutomorphicForm_forall_integrableOn_and_setIntegral_lambdaT_mul_tsum_convOp_mul_conj_eq_mul_tsum_cutTrace
end P2MW
export P2MW.S_AutomorphicForm_forall_integrableOn_and_setIntegral_lambdaT_mul_tsum_convOp_mul_conj_eq_mul_tsum_cutTrace (solution)
