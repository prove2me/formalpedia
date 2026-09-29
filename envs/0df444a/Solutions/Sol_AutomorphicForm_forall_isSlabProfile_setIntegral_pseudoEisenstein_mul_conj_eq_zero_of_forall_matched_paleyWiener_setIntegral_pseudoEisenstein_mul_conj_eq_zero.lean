-- Prove2me | solution 1 for AutomorphicForm.forall_isSlabProfile_setIntegral_pseudoEisenstein_mul_conj_eq_zero_of_forall_matched_paleyWiener_setIntegral_pseudoEisenstein_mul_conj_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/8e502c17-4c0c-5488-9347-a97770806c81

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
import Mathlib
import Theorems.Thm_AutomorphicForm_exists_isSlabProfile_paleyWiener_eLpNorm_sub_restrict_rationalTorusUnipotentQuotient_lt_of_isSlabProfile
import Theorems.Thm_AutomorphicForm_PseudoEisensteinSlab_eLpNorm_pseudoEisenstein_le_of_adelicHeight_mem_Icc
import Theorems.Thm_AutomorphicForm_isAutomorphicFnAt_pseudoEisenstein_slab
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_AutomorphicForm_finite_support_pseudoEisenstein_summand
import Theorems.Thm_AutomorphicForm_paleyWiener_levelTypeAverage_and_pseudoEisenstein_levelTypeAverage_eq_and_residualProjection_of_kernel_maximalCompact_detOne
import Theorems.Thm_AutomorphicForm_setIntegral_levelTypeAverage_mul_conj_eq_and_eLpNorm_levelTypeAverage_le_of_isAutomorphicFnAt_of_idempotent_kernel_maximalCompact
import Theorems.Thm_AutomorphicForm_levelTypeAverage_ae_eq_self_of_isAutomorphicFnAt_of_mem_archCutSubmodule
import Theorems.Thm_AutomorphicForm_exists_continuous_idempotent_kernel_maximalCompact_comm_rowIsometry_levelTypeAverage_eq_self_and_mem_archCutSubmodule
import Theorems.Thm_AutomorphicForm_exists_isInducedSection_swap_ne_zero_of_isInducedSection_family_principalLevel_archCutSubmodule_of_apply_ne_zero
import Theorems.Thm_AutomorphicForm_exists_forall_eq_mul_normPowChar_and_eq_mul_normPowChar_inv_of_pairs_of_exists_isInducedSection
import Theorems.Thm_AutomorphicForm_mem_span_chiDet_continuous_of_mem_residualSpan_of_isAutomorphicFnAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_forall_isSlabProfile_setIntegral_pseudoEisenstein_mul_conj_eq_zero_of_forall_matched_paleyWiener_setIntegral_pseudoEisenstein_mul_conj_eq_zero
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions"
p2m_attr_erase "simp" "AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"
p2m_attr_erase "simp" "M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.Bridge.finiteConorm_apply AutomorphicForm.JPSSCubicLiftPackage.mk.sizeOf_spec AutomorphicForm.formalBaseChange_a AutomorphicForm.JPSSCubicLiftPackage.mk.injEq AutomorphicForm.formalBaseChange_b M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11 AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22LocalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_right ContinuousAddEquiv.preimage_mulLeft_smul AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace ExtDensAux
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

theorem memLp_conj {μ : Measure α} {v : α → ℂ} (hv : MemLp v 2 μ) :
    MemLp (fun a => conj (v a)) 2 μ :=
  MemLp.of_le hv (Complex.continuous_conj.comp_aestronglyMeasurable hv.1)
    (Filter.Eventually.of_forall fun a => by simp)

theorem integrable_mul_conj {μ : Measure α} {F v : α → ℂ}
    (hF : MemLp F 2 μ) (hv : MemLp v 2 μ) : Integrable (fun a => F a * conj (v a)) μ := by
  have h : MemLp (F * fun a => conj (v a)) 1 μ := MemLp.mul (memLp_conj hv) hF
  rw [memLp_one_iff_integrable] at h
  exact h

theorem norm_integral_mul_conj_le (μ : Measure α) (F v : α → ℂ)
    (hF : MemLp F 2 μ) (hv : MemLp v 2 μ) :
    ‖∫ a, F a * conj (v a) ∂μ‖ ≤ (eLpNorm F 2 μ).toReal * (eLpNorm v 2 μ).toReal := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (hv.toLp v) (hF.toLp F)
  rw [MeasureTheory.L2.inner_def] at h
  have hc : ∫ a, (inner ℂ ((hv.toLp v) a) ((hF.toLp F) a)) ∂μ = ∫ a, F a * conj (v a) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hv.coeFn_toLp, hF.coeFn_toLp] with a ha hb
    rw [ha, hb, RCLike.inner_apply]
  rw [hc, Lp.norm_toLp, Lp.norm_toLp, mul_comm] at h
  exact h

theorem integral_mul_conj_eq_zero_of_approx (μ : Measure α) (D θ : α → ℂ)
    (hD : MemLp D 2 μ) (hθ : MemLp θ 2 μ)
    (h : ∀ ε > (0:ℝ), ∃ θ' : α → ℂ, MemLp θ' 2 μ ∧ eLpNorm (θ - θ') 2 μ ≤ ENNReal.ofReal ε ∧
      ∫ a, D a * conj (θ' a) ∂μ = 0) :
    ∫ a, D a * conj (θ a) ∂μ = 0 := by
  by_contra hne
  have hpos : 0 < ‖∫ a, D a * conj (θ a) ∂μ‖ := norm_pos_iff.mpr hne
  set I : ℝ := ‖∫ a, D a * conj (θ a) ∂μ‖ with hI
  set M : ℝ := (eLpNorm D 2 μ).toReal with hM
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  obtain ⟨θ', hθ', hclose, hzero⟩ := h (I / (2 * (M + 1))) (by positivity)
  have iθ := integrable_mul_conj hD hθ
  have iθ' := integrable_mul_conj hD hθ'
  have key : ∫ a, D a * conj (θ a) ∂μ = ∫ a, D a * conj ((θ - θ') a) ∂μ := by
    have : (fun a => D a * conj ((θ - θ') a)) = fun a => D a * conj (θ a) - D a * conj (θ' a) := by
      funext a; simp [mul_sub]
    rw [this, integral_sub iθ iθ', hzero, sub_zero]
  have hcs := norm_integral_mul_conj_le μ D (θ - θ') hD (hθ.sub hθ')
  have hreal : (eLpNorm (θ - θ') 2 μ).toReal ≤ I / (2 * (M + 1)) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hclose
  have h1 : I ≤ M * (I / (2 * (M + 1))) := by
    calc I = ‖∫ a, D a * conj ((θ - θ') a) ∂μ‖ := by rw [hI, key]
      _ ≤ M * (eLpNorm (θ - θ') 2 μ).toReal := hcs
      _ ≤ M * (I / (2 * (M + 1))) := mul_le_mul_of_nonneg_left hreal hM0
  have hM1 : M / (2 * (M + 1)) < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  have h2 : M * (I / (2 * (M + 1))) < I := by
    calc M * (I / (2 * (M + 1))) = (M / (2 * (M + 1))) * I := by ring
      _ < 1 * I := mul_lt_mul_of_pos_right hM1 hpos
      _ = I := one_mul _
  exact absurd (h1.trans_lt h2) (lt_irrefl _)

theorem integral_mul_conj_eq_zero_of_approx' (μ : Measure α) (D θ : α → ℂ)
    (hD : MemLp D 2 μ) (hθ : MemLp θ 2 μ)
    (h : ∀ ε > (0:ℝ), ∃ θ' : α → ℂ, MemLp θ' 2 μ ∧ eLpNorm (θ - θ') 2 μ ≤ ENNReal.ofReal ε ∧
      ∫ a, θ' a * conj (D a) ∂μ = 0) :
    ∫ a, θ a * conj (D a) ∂μ = 0 := by
  have hconj : ∀ (F G : α → ℂ), ∫ a, F a * conj (G a) ∂μ = conj (∫ a, G a * conj (F a) ∂μ) := by
    intro F G
    rw [← integral_conj]
    congr 1; funext a; simp [mul_comm]
  rw [hconj, integral_mul_conj_eq_zero_of_approx μ D θ hD hθ ?_, map_zero]
  intro ε hε
  obtain ⟨θ', hθ', hc, hz⟩ := h ε hε
  refine ⟨θ', hθ', hc, ?_⟩
  rw [hconj, hz, map_zero]

end ExtDensAux

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
      (f : AdelicGL2 (𝓞 K) K → ℂ)
      (_hf : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK f)
      (_hflev : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).U N, f (g * u) = f g)
      (_hfty : f ∈ archCutSubmodule K tysK)
      (_horth : ∀
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
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
            AutomorphicForm.pseudoEisenstein K ψ g * conj (f g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (χ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hχ : AutomorphicForm.IsSlabProfile K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK χ),
    ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        AutomorphicForm.pseudoEisenstein K χ g * conj (f g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 := by
  intro αm hαm ιE _iE μ ν hμ hν hμic hνic hμc hνc hμν hdist nE φE hφE hφEK hφEf
    hφEjc hφEhol hφEKu hφEflat hφElev hφEty hφEon hφEspan hpairs OE EE NE hEE f hf hflev hfty horth χ hχ

  have hNbot : N ≠ ⊥ := by
    intro hN0
    have hall : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ SK := fun v =>
      hN v (by rw [hN0]; exact ⟨⊥, by simp⟩)
    have hker : RingHom.ker (algebraMap ℤ (𝓞 K)) ≤ ⊥ :=
      ((RingHom.injective_iff_ker_eq_bot _).mp (RingHom.injective_int _)).le
    have key : ∀ p : Nat.Primes, ∃ v : HeightOneSpectrum (𝓞 K),
        v.asIdeal.comap (algebraMap ℤ (𝓞 K)) = Ideal.span {(p : ℤ)} := by
      intro p
      have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp p.2
      have hp0 : (p : ℤ) ≠ 0 := hp.ne_zero
      haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
        ((Ideal.span_singleton_prime hp0).mpr hp).isMaximal (by simpa [Ideal.span_singleton_eq_bot] using hp0)
      obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K)
        (Ideal.span {(p : ℤ)}) (le_trans hker bot_le)
      have hQbot : Q ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hQmax (RingOfIntegers.not_isField K)
      exact ⟨⟨Q, hQmax.isPrime, hQbot⟩, hQ⟩
    choose vp hvp using key
    have hinj : Function.Injective vp := by
      intro p q hpq
      have h := hvp p
      rw [hpq, hvp q] at h
      have h' : Associated (q : ℤ) (p : ℤ) := Ideal.span_singleton_eq_span_singleton.mp h
      have hn : (q : ℤ).natAbs = (p : ℤ).natAbs := Int.natAbs_eq_iff_associated.mpr h'
      exact Subtype.ext (by simpa using hn.symm)
    haveI : Infinite Nat.Primes := Set.infinite_coe_iff.mpr Nat.infinite_setOf_prime
    haveI : Infinite (HeightOneSpectrum (𝓞 K)) := Infinite.of_injective vp hinj
    have hfin : Finite (HeightOneSpectrum (𝓞 K)) :=
      Finite.of_injective (fun v => (⟨v, hall v⟩ : {v // v ∈ SK}))
        (fun a b h => congrArg Subtype.val h)
    exact not_finite (HeightOneSpectrum (𝓞 K))
  obtain ⟨-, -, -, hΦs, hΦ⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ
  have hξK : Continuous ξK := by
    have h1 : Continuous (fun w : ↥(⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) => ((ξK w : ℂˣ) : ℂ)) :=
      hξc.comp continuous_subtype_val
    have h2 : Continuous (fun w : ↥(⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) => (((ξK w)⁻¹ : ℂˣ) : ℂ)) := by
      simp only [Units.val_inv_eq_inv_val]
      exact h1.inv₀ (fun w => (ξK w).ne_zero)
    exact Units.continuous_iff.mpr ⟨h1, h2⟩

  have hmem : ∀ {u : AdelicGL2 (𝓞 K) K → ℂ}, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u → MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) :=
    fun {u} hu => ((AutomorphicForm.lsXiMemberAt_iff (𝓞 K) K (adelicGLHaar (Fin 2) (𝓞 K) K) ⊤ ξK
      (AutomorphicForm.canonicalTruncationDomain K α β) u).1 hu).2
  have hθχ := AutomorphicForm.isAutomorphicFnAt_pseudoEisenstein_slab K α β hα hαβ
    (AutomorphicForm.canonicalTruncationDomain K α β) hΦs hΦ ξK χ hχ
  have hflev' : ∀ (g : AdelicGL2 (𝓞 K) K), ∀ u' ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
      f (g * u') = f g := fun g u hu => hflev g u hu

  refine ExtDensAux.integral_mul_conj_eq_zero_of_approx' ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) f (AutomorphicForm.pseudoEisenstein K χ)
    (hmem hf) (hmem hθχ) ?_
  intro ε hε

  have hξu' : ∀ z : (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
      (fun N => levelOne (𝓞 K) K N) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z, ‖((ξK z : ℂˣ) : ℂ)‖ = 1 :=
    fun z => hξu z
  obtain ⟨a₀, b₀, ha₀, hbandχ, hS4⟩ :=
    AutomorphicForm.exists_isSlabProfile_paleyWiener_eLpNorm_sub_restrict_rationalTorusUnipotentQuotient_lt_of_isSlabProfile K hαm
      α β hα hαβ (AutomorphicForm.canonicalTruncationDomain K α β) ξK hξK hξu' χ hχ
  obtain ⟨C, hC⟩ := AutomorphicForm.PseudoEisensteinSlab.eLpNorm_pseudoEisenstein_le_of_adelicHeight_mem_Icc K α β
    (AutomorphicForm.canonicalTruncationDomain K α β) hΦs hΦ a₀ b₀ ha₀
  set δ : ℝ := ε / ((C : ℝ) + 1) with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨ιP, instP, μP, νP, rP, ψf, ψ₀, hμP, hνP, hμPic, hνPic, hμPc, hνPc, hμνP, hrP, hdistP, hψf, hψjc, hψhol,
    hψK, hψsm, hψKu, hψdec, hψ₀, hψrep, hψband, hψlt⟩ := hS4 δ hδpos

  obtain ⟨κ, hκc, hκs, hκi, hκcomm, hFIX, hRANGE, hIDEM⟩ :=
    AutomorphicForm.exists_continuous_idempotent_kernel_maximalCompact_comm_rowIsometry_levelTypeAverage_eq_self_and_mem_archCutSubmodule K ξK hξu N hNbot tysK
  have hL2 := AutomorphicForm.setIntegral_levelTypeAverage_mul_conj_eq_and_eLpNorm_levelTypeAverage_le_of_isAutomorphicFnAt_of_idempotent_kernel_maximalCompact K α β hα hαβ ξK κ hκc hκs hκi

  obtain ⟨P, hP⟩ : ∃ P : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ),
      ∀ (φ : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K),
        P φ g = ∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) := ⟨_, fun _ _ => rfl⟩
  have hPfun : ∀ φ : AdelicGL2 (𝓞 K) K → ℂ,
      (fun g : AdelicGL2 (𝓞 K) K => ∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) = P φ :=
    fun φ => funext (fun g => (hP φ g).symm)
  simp only [← hP] at hRANGE hL2

  have hPres : ∀ h : AdelicGL2 (𝓞 K) K → ℂ,
      IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
      h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK →
      P h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK := by
    intro h hh hres
    haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
    have hspan := AutomorphicForm.mem_span_chiDet_continuous_of_mem_residualSpan_of_isAutomorphicFnAt K α β hα hαβ ξK hξc
      h hres hh
    have hdet : Continuous (fun g : AdelicGL2 (𝓞 K) K => Matrix.GeneralLinearGroup.det g) := by
      refine Units.continuous_iff.mpr ⟨?_, ?_⟩
      · have h1 : Continuous fun g : AdelicGL2 (𝓞 K) K => ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).det :=
          Units.continuous_val.matrix_det
        exact h1
      · have h1 : Continuous fun g : AdelicGL2 (𝓞 K) K => (((g⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).det :=
          (Units.continuous_val.comp continuous_inv).matrix_det
        have : (fun g : AdelicGL2 (𝓞 K) K => (((Matrix.GeneralLinearGroup.det g)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) =
            fun g : AdelicGL2 (𝓞 K) K => (((g⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).det := by
          funext g; rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
        rw [this]; exact h1
    have key : ∀ f ∈ Submodule.span ℂ ((fun χ => chiDet (𝓞 K) K χ) '' {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
        SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range → χ z = 1) ∧
        Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)}),
        (∀ g : AdelicGL2 (𝓞 K) K, Integrable (fun k : ↥(adelicMaximalCompact K) => κ k * f (g * (k : AdelicGL2 (𝓞 K) K))) (maximalCompactHaar K)) ∧
        P f ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK := by
      intro f hf
      induction hf using Submodule.span_induction with
      | mem f hfS =>
        obtain ⟨χ, ⟨hsq, -, hχc⟩, rfl⟩ := hfS
        have hmul : ∀ (g : AdelicGL2 (𝓞 K) K) (k : ↥(adelicMaximalCompact K)),
            chiDet (𝓞 K) K χ (g * (k : AdelicGL2 (𝓞 K) K)) = chiDet (𝓞 K) K χ g * chiDet (𝓞 K) K χ (k : AdelicGL2 (𝓞 K) K) := by
          intro g k; simp [AutomorphicForm.chiDet, map_mul]
        have hcont : Continuous (fun k : ↥(adelicMaximalCompact K) => κ k * chiDet (𝓞 K) K χ (k : AdelicGL2 (𝓞 K) K)) := by
          refine hκc.mul ?_
          exact hχc.comp (hdet.comp continuous_subtype_val)
        have hint : Integrable (fun k : ↥(adelicMaximalCompact K) => κ k * chiDet (𝓞 K) K χ (k : AdelicGL2 (𝓞 K) K))
            (maximalCompactHaar K) :=
          hcont.integrable_of_hasCompactSupport
            (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))
        refine ⟨fun g => ?_, ?_⟩
        · have : (fun k : ↥(adelicMaximalCompact K) => κ k * chiDet (𝓞 K) K χ (g * (k : AdelicGL2 (𝓞 K) K))) =
              fun k => chiDet (𝓞 K) K χ g * (κ k * chiDet (𝓞 K) K χ (k : AdelicGL2 (𝓞 K) K)) := by
            funext k; rw [hmul]; ring
          rw [this]; exact hint.const_mul _
        · have hPχ : P (chiDet (𝓞 K) K χ) =
              (∫ k, κ k * chiDet (𝓞 K) K χ (k : AdelicGL2 (𝓞 K) K) ∂(maximalCompactHaar K)) • chiDet (𝓞 K) K χ := by
            funext g
            rw [hP, Pi.smul_apply, smul_eq_mul]
            have : (fun k : ↥(adelicMaximalCompact K) => κ k * chiDet (𝓞 K) K χ (g * (k : AdelicGL2 (𝓞 K) K))) =
                fun k => chiDet (𝓞 K) K χ g * (κ k * chiDet (𝓞 K) K χ (k : AdelicGL2 (𝓞 K) K)) := by
              funext k; rw [hmul]; ring
            rw [this, integral_const_mul, mul_comm]
          rw [hPχ]
          exact Submodule.smul_mem _ _ (AutomorphicForm.chiDet_mem_residualSpan hsq)
      | zero =>
        refine ⟨fun g => by simp, ?_⟩
        have : P 0 = 0 := by funext g; rw [hP]; simp
        rw [this]; exact Submodule.zero_mem _
      | add f₁ f₂ _ _ ih₁ ih₂ =>
        refine ⟨fun g => ?_, ?_⟩
        · have : (fun k : ↥(adelicMaximalCompact K) => κ k * (f₁ + f₂) (g * (k : AdelicGL2 (𝓞 K) K))) =
              fun k => κ k * f₁ (g * (k : AdelicGL2 (𝓞 K) K)) + κ k * f₂ (g * (k : AdelicGL2 (𝓞 K) K)) := by
            funext k; simp only [Pi.add_apply, mul_add]
          rw [this]; exact (ih₁.1 g).add (ih₂.1 g)
        · have : P (f₁ + f₂) = P f₁ + P f₂ := by
            funext g
            rw [Pi.add_apply, hP, hP, hP, ← integral_add (ih₁.1 g) (ih₂.1 g)]
            congr 1; funext k; simp only [Pi.add_apply, mul_add]
          rw [this]; exact Submodule.add_mem _ ih₁.2 ih₂.2
      | smul c f _ ih =>
        refine ⟨fun g => ?_, ?_⟩
        · have : (fun k : ↥(adelicMaximalCompact K) => κ k * (c • f) (g * (k : AdelicGL2 (𝓞 K) K))) =
              fun k => c * (κ k * f (g * (k : AdelicGL2 (𝓞 K) K))) := by
            funext k; simp only [Pi.smul_apply, smul_eq_mul]; ring
          rw [this]; exact (ih.1 g).const_mul c
        · have : P (c • f) = c • P f := by
            funext g
            rw [Pi.smul_apply, hP, hP, smul_eq_mul, ← integral_const_mul]
            congr 1; funext k; simp only [Pi.smul_apply, smul_eq_mul]; ring
          rw [this]; exact Submodule.smul_mem _ _ ih.2
    exact (key h hspan).2

  obtain ⟨hTf, hTjc, hThol, hTK, hTsm, hTKu, hTdec, hTψ, hTrep, hTlev, hTty, hTθ, hTres⟩ :=
    AutomorphicForm.paleyWiener_levelTypeAverage_and_pseudoEisenstein_levelTypeAverage_eq_and_residualProjection_of_kernel_maximalCompact_detOne K α β hα hαβ ξK hξc hξt hξu N tysK hαm κ hκc
      P hP hRANGE
      (fun φ k hk g => by rw [hP, hP]; exact hκcomm φ k hk g) (fun φ ψ hφ hψ => ⟨(hL2 φ ψ hφ hψ).1, (hL2 φ ψ hφ hψ).2.1⟩) hPres
      ιP μP νP hμP hνP hμPic hνPic hμPc hμνP rP hrP hdistP ψf hψf hψjc hψhol hψK hψsm hψKu hνPc hψdec ψ₀ hψ₀ hψrep
  have hθ₀ := AutomorphicForm.isAutomorphicFnAt_pseudoEisenstein_slab K α β hα hαβ
    (AutomorphicForm.canonicalTruncationDomain K α β) hΦs hΦ ξK ψ₀ hψ₀

  classical
  have hrr : ∀ e : ιP, rP (rP e) = e := by
    intro e
    by_contra hne
    obtain ⟨x, -, hx⟩ := hdistP (rP (rP e)) e hne
    rcases hx with hx | hx
    · exact hx (by rw [(hrP (rP e)).1, (hrP e).2])
    · exact hx (by rw [(hrP (rP e)).2, (hrP e).1])
  let Pψf : ιP → ℂ → AdelicGL2 (𝓞 K) K → ℂ := fun i s => P (ψf i s)
  let kept : ιP → Prop := fun i => ∃ (t : ℝ) (g : AdelicGL2 (𝓞 K) K), Pψf i ((t : ℂ) * Complex.I) g ≠ 0
  let ιP' : Type := {i : ιP // kept i ∨ kept (rP i)}
  letI instP' : Fintype ιP' := Subtype.fintype _
  let rP' : ιP' → ιP' := fun i => ⟨rP i.1, by
    rcases i.2 with h | h
    · exact Or.inr (by rw [hrr]; exact h)
    · exact Or.inl h⟩

  have hdrop : ∀ i : ιP, ¬ (kept i ∨ kept (rP i)) → ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K), Pψf i s g = 0 := by
    intro i hi s g
    have hax : ∀ (t : ℝ), Pψf i ((t : ℂ) * Complex.I) g = 0 := by
      intro t
      by_contra hne
      exact hi (Or.inl ⟨t, g, hne⟩)

    have hF : AnalyticOnNhd ℂ (fun s => Pψf i s g) Set.univ :=
      (hThol i g).differentiableOn.analyticOnNhd isOpen_univ
    have hfr : ∃ᶠ z in nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ, (fun s => Pψf i s g) z = 0 := by
      rw [Filter.frequently_iff]
      intro U hU
      obtain ⟨r, hr, hrU⟩ := Metric.mem_nhdsWithin_iff.mp hU
      refine ⟨((r / 2 : ℝ) : ℂ) * Complex.I, hrU ⟨?_, ?_⟩, hax (r / 2)⟩
      · rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by positivity)]
        linarith
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, mul_eq_zero, Complex.ofReal_eq_zero,
          Complex.I_ne_zero, or_false]
        exact (by positivity : (r / 2 : ℝ) ≠ 0)
    have h0 := hF.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (Set.mem_univ 0) hfr
    exact h0 (Set.mem_univ s)

  have hsec : ∀ i : ιP', ∃ (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
      IsInducedSection (𝓞 K) K (etaFst (μP i.1) αm hαm ((t : ℂ) * Complex.I)) (etaSnd (νP i.1) αm hαm ((t : ℂ) * Complex.I)) φ₀ ∧
      Continuous φ₀ ∧ IsArchKFinite K φ₀ ∧
      (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) ∧
      φ₀ ∈ archCutSubmodule K tysK ∧ φ₀ ≠ 0 := by
    intro i
    rcases i.2 with hk | hk
    · obtain ⟨t, g, hne⟩ := hk
      refine ⟨t, Pψf i.1 ((t : ℂ) * Complex.I), hTf i.1 _, ?_, hTK i.1 _, hTlev i.1 _, hTty i.1 _, ?_⟩
      · exact (hTjc i.1).comp (Continuous.prodMk continuous_const continuous_id)
      · intro h0
        exact hne (by simp only [Pψf] at h0 ⊢; exact congrFun h0 g)
    · obtain ⟨t, g, hne⟩ := hk
      have hsw := AutomorphicForm.exists_isInducedSection_swap_ne_zero_of_isInducedSection_family_principalLevel_archCutSubmodule_of_apply_ne_zero K N tysK hαm
        (μP (rP i.1)) (νP (rP i.1)) (hμP _) (hνP _) (hμPic _) (hνPic _) (hμPc _) (hνPc _)
        (Pψf (rP i.1)) (hTf _) (hTK _) (hTsm _) (hTjc _) (hThol _) (hTKu _) (hTlev _) (hTty _) ⟨t, g, hne⟩
      obtain ⟨t', φ₀, hφ₀, hφ₀c, hφ₀K, hφ₀lev, hφ₀ty, hφ₀ne⟩ := hsw
      refine ⟨t', φ₀, ?_, hφ₀c, hφ₀K, hφ₀lev, hφ₀ty, hφ₀ne⟩
      rw [(hrP i.1).1, (hrP i.1).2] at hφ₀
      exact hφ₀
  obtain ⟨em, τ, hem⟩ :=
    AutomorphicForm.exists_forall_eq_mul_normPowChar_and_eq_mul_normPowChar_inv_of_pairs_of_exists_isInducedSection K ξK N tysK hαm
      ιE μ ν hμ hν hμic hνic hμc hνc hμν hpairs ιP' (fun i => μP i.1) (fun i => νP i.1)
      (fun i => hμP i.1) (fun i => hνP i.1) (fun i => hμPic i.1) (fun i => hνPic i.1)
      (fun i => hμPc i.1) (fun i => hνPc i.1) (fun i z => hμνP i.1 ⟨z, Subgroup.mem_top z⟩) hsec

  have hrep' : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
      P ψ₀ g = ∑ i : ιP', (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
        ∫ t : ℝ, Pψf i.1 ((σ' : ℂ) + (t : ℂ) * Complex.I) g := by
    intro σ' g
    rw [hTrep σ' g, ← Fintype.sum_subtype_add_sum_subtype (fun i : ιP => kept i ∨ kept (rP i))]
    have h0 : ∑ i : {i : ιP // ¬ (kept i ∨ kept (rP i))}, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
        ∫ t : ℝ, Pψf i.1 ((σ' : ℂ) + (t : ℂ) * Complex.I) g = 0 := by
      refine Finset.sum_eq_zero (fun i _ => ?_)
      simp [hdrop i.1 i.2]
    simp only [Pψf] at h0 ⊢
    rw [h0, add_zero]

  have hzero : ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
      AutomorphicForm.pseudoEisenstein K (P ψ₀) g * conj (f g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 :=
    horth ιP' (fun i => μP i.1) (fun i => νP i.1)
      (fun i => hμP i.1) (fun i => hνP i.1) (fun i => hμPic i.1) (fun i => hνPic i.1) (fun i => hμPc i.1)
      (fun i z => hμνP i.1 z) rP' (fun i => ⟨(hrP i.1).1, (hrP i.1).2⟩)
      (fun i j hij => hdistP i.1 j.1 (fun h => hij (Subtype.ext h)))
      (fun i s => Pψf i.1 s) (fun i => hTf i.1) (fun i => hTjc i.1) (fun i => hThol i.1) (fun i => hTK i.1)
      (fun i => hTsm i.1) (fun i => hTKu i.1) (fun i => hνPc i.1) (fun i => hTdec i.1)
      (P ψ₀) hTψ hrep' em τ hem (fun i => hTlev i.1) (fun i => hTty i.1)

  obtain ⟨-, hadj, -⟩ := hL2 (AutomorphicForm.pseudoEisenstein K ψ₀) f hθ₀ hf
  have hfix := AutomorphicForm.levelTypeAverage_ae_eq_self_of_isAutomorphicFnAt_of_mem_archCutSubmodule K α β hα hαβ ξK hξc hξt hξu N hNbot tysK κ hκc hFIX f hf hflev' hfty
  rw [hPfun] at hfix
  have hpair : ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
      AutomorphicForm.pseudoEisenstein K ψ₀ g * conj (f g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 := by
    calc ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          AutomorphicForm.pseudoEisenstein K ψ₀ g * conj (f g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
        = ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          AutomorphicForm.pseudoEisenstein K ψ₀ g * conj (P f g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
            integral_congr_ae (hfix.mono fun g hg => by simp [hg])
      _ = ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          P (AutomorphicForm.pseudoEisenstein K ψ₀) g * conj (f g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := hadj.symm
      _ = ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          AutomorphicForm.pseudoEisenstein K (P ψ₀) g * conj (f g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by rw [hTθ]
      _ = 0 := hzero
  refine ⟨AutomorphicForm.pseudoEisenstein K ψ₀, hmem hθ₀, ?_, hpair⟩

  have hlin : AutomorphicForm.pseudoEisenstein K χ - AutomorphicForm.pseudoEisenstein K ψ₀ =
      AutomorphicForm.pseudoEisenstein K (χ - ψ₀) := by
    funext g
    have hs₁ : Summable (fun b : K => χ (adelicWeyl (𝓞 K) K * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) b) * g)) :=
      summable_of_ne_finset_zero (s := (AutomorphicForm.finite_support_pseudoEisenstein_summand K _ ξK χ hχ g).toFinset)
        (fun b hb => by rwa [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hb)
    have hs₂ : Summable (fun b : K => ψ₀ (adelicWeyl (𝓞 K) K * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) b) * g)) :=
      summable_of_ne_finset_zero (s := (AutomorphicForm.finite_support_pseudoEisenstein_summand K _ ξK ψ₀ hψ₀ g).toFinset)
        (fun b hb => by rwa [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hb)
    simp only [Pi.sub_apply, AutomorphicForm.pseudoEisenstein_apply]
    rw [hs₁.tsum_sub hs₂]
    ring
  rw [hlin]
  have hmeas : Measurable (χ - ψ₀) := hχ.measurable.sub hψ₀.measurable
  have hunip : ∀ (x : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K), (χ - ψ₀) (unipotentGL2 x * g) = (χ - ψ₀) g :=
    fun x g => by simp only [Pi.sub_apply, hχ.unipotent_mul, hψ₀.unipotent_mul]
  have hbor : ∀ γ ∈ borelSubgroup K, ∀ g : AdelicGL2 (𝓞 K) K, (χ - ψ₀) (globalPoints (𝓞 K) K γ * g) = (χ - ψ₀) g :=
    fun γ hγ g => by simp only [Pi.sub_apply, hχ.borel_mul γ hγ, hψ₀.borel_mul γ hγ]
  have hband : ∀ g : AdelicGL2 (𝓞 K) K, (χ - ψ₀) g ≠ 0 → NumberField.AdelicHeight.adelicHeight K g ∈ Set.Icc a₀ b₀ := by
    intro g hg
    by_cases h1 : χ g ≠ 0
    · exact hbandχ g h1
    · push Not at h1
      have h2 : ψ₀ g ≠ 0 := by
        intro h0; exact hg (by simp [h1, h0])
      exact hψband g h2
  have hCb := hC (χ - ψ₀) hmeas hunip hbor hband
  have hCδ : ((C : ℝ) + 1) * δ = ε := by
    rw [hδ]; field_simp
  have hCδ' : (C : ℝ) * δ ≤ ε := by nlinarith [hδpos, C.coe_nonneg]
  calc eLpNorm (AutomorphicForm.pseudoEisenstein K (χ - ψ₀)) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))
      ≤ (C : ENNReal) * eLpNorm (fun q : AutomorphicForm.RationalTorusUnipotentQuotient K => (χ - ψ₀) q.out) 2
          ((AutomorphicForm.rationalTorusUnipotentQuotientMeasure K).restrict
            {q | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det q.out) ∈ Set.Icc α β}) := hCb
    _ ≤ (C : ENNReal) * ENNReal.ofReal δ := by gcongr; exact hψlt.le
    _ = ENNReal.ofReal ((C : ℝ) * δ) := by
        rw [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal]
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hCδ'

end

end S_AutomorphicForm_forall_isSlabProfile_setIntegral_pseudoEisenstein_mul_conj_eq_zero_of_forall_matched_paleyWiener_setIntegral_pseudoEisenstein_mul_conj_eq_zero
end P2MW
export P2MW.S_AutomorphicForm_forall_isSlabProfile_setIntegral_pseudoEisenstein_mul_conj_eq_zero_of_forall_matched_paleyWiener_setIntegral_pseudoEisenstein_mul_conj_eq_zero (solution)
