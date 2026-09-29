-- Prove2me | solution 1 for AutomorphicForm.CuspidalSpectrum.exists_isLevelSphericalOfType_flat_norm_toCuspSubcarrier_sub_lt_of_forall_apply_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/81e0a664-56ad-53c4-a126-85ee4efedfef

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ArchSpherical
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_nhds_forall_norm_toCarrier_rightTranslate_sub_lt
import Theorems.Thm_AutomorphicForm_exists_isArchTestFactor_nonneg_and_tsupport_subset_and_conj_invariant_and_flat
import Theorems.Thm_AutomorphicForm_exists_continuous_conj_invariant_integral_mul_apply_mul_eq_of_finiteDimensional_of_le_archCutSubmodule
import Theorems.Thm_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule
import Theorems.Thm_AutomorphicForm_integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat
import Theorems.Thm_AutomorphicForm_isCompact_rowIsometrySubgroup_detOne
import Theorems.Thm_AutomorphicForm_exists_pos_forall_rightConv_integral_prod_mul_indicator_eq_mul_integral_of_forall_integral_mul_apply_mul_eq
import Theorems.Thm_MeasureTheory_lintegral_enorm_sub_integral_mul_sq_le_lintegral_mul_lintegral_enorm_sub_sq
import Theorems.Thm_AutomorphicForm_finiteDimensional_span_translates_of_mem_archCutSubmodule
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_of_isHaarMeasure_generalLinearGroup_infiniteAdeleRing
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_rightConv_mem_cuspMemberSubmodule
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_isLevelSphericalOfType_flat_norm_toCuspSubcarrier_sub_lt_of_forall_apply_mul_eq
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"
p2m_attr_erase "simp" "AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open scoped Topology
open Filter

noncomputable section

namespace T6Assembly

variable {F : Type} [Field F] [NumberField F]

private def iota (F : Type) [Field F] [NumberField F] :
    (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* GL (Fin 2) (InfiniteAdeleRing F) :=
  (Units.map (Matrix.piRingEquiv (β := fun w : InfinitePlace F => w.Completion) (n := Fin 2)).symm.toRingHom.toMonoidHom).comp
    ((MulEquiv.piUnits (M := fun w : InfinitePlace F => Matrix (Fin 2) (Fin 2) w.Completion)).symm.toMonoidHom.comp
      (MonoidHom.pi fun w : InfinitePlace F =>
        (rowIsometrySubgroup₀ w.Completion).subtype.comp
          (Pi.evalMonoidHom (fun w : InfinitePlace F => ↥(rowIsometrySubgroup₀ w.Completion)) w)))

private theorem iota_apply_val (κ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) (i j : Fin 2) (w : InfinitePlace F) :
    ((iota F κ : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j w
      = (((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j :=
  rfl

private theorem archComponent_iota (κ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) (w : InfinitePlace F) :
    archComponent F w (iota F κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) := by
  ext i j
  rfl

private theorem continuous_iota : Continuous (iota F) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => continuous_pi fun w => ?_
    show Continuous fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) =>
      (((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j
    exact (Units.continuous_val.matrix_elem i j).comp (continuous_subtype_val.comp (continuous_apply w))
  · refine continuous_matrix fun i j => continuous_pi fun w => ?_
    have : (fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) =>
        (((iota F κ)⁻¹ : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j w)
        = fun κ => ((((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion)⁻¹ : GL (Fin 2) w.Completion) :
            Matrix (Fin 2) (Fin 2) w.Completion) i j := by
      funext κ
      rw [← map_inv]
      rfl
    rw [this]
    exact (Units.continuous_coe_inv.matrix_elem i j).comp (continuous_subtype_val.comp (continuous_apply w))

private theorem eq_of_isMulLeftInvariant_of_isProbabilityMeasure {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] (μ' μ : Measure G)
    [μ.IsHaarMeasure] [IsProbabilityMeasure μ] [μ'.IsMulLeftInvariant] [IsProbabilityMeasure μ'] : μ' = μ := by
  have h := Measure.isMulInvariant_eq_smul_of_compactSpace μ' μ
  have hc : Measure.haarScalarFactor μ' μ = 1 := by
    have h1 := congrArg (fun ν : Measure G => ν Set.univ) h
    simp only [Measure.smul_apply, measure_univ] at h1
    rw [ENNReal.smul_def, smul_eq_mul, mul_one] at h1
    exact_mod_cast h1.symm
  rw [h, hc, one_smul]

private theorem eLpNorm_two_pow_two {α : Type*} [MeasurableSpace α] (ν : Measure α) (φ : α → ℂ) :
    eLpNorm φ 2 ν ^ 2 = ∫⁻ a, ‖φ a‖ₑ ^ 2 ∂ν := by
  rw [eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat,
    ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

private theorem norm_toCarrier_sub {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (a b : AdelicGL2 (𝓞 F) F → ℂ)
    (ha : a ∈ memberSubmodule F Φ₀ ξ) (hb : b ∈ memberSubmodule F Φ₀ ξ) :
    ‖toCarrier F hΦ₀ σ ξ ⟨a, ha⟩ - toCarrier F hΦ₀ σ ξ ⟨b, hb⟩‖ = (eLpNorm (a - b) 2 (weightedMeasure F Φ₀ σ)).toReal := by
  rw [← map_sub]
  have : (⟨a, ha⟩ - ⟨b, hb⟩ : ↥(memberSubmodule F Φ₀ ξ)) = ⟨a - b, (memberSubmodule F Φ₀ ξ).sub_mem ha hb⟩ := rfl
  rw [this]
  exact Lp.norm_toLp (a - b) (memLp_weightedMeasure_of_mem F hΦ₀ σ ((memberSubmodule F Φ₀ ξ).sub_mem ha hb))

private theorem eLpNorm_sub_lt_top {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ} {a b : AdelicGL2 (𝓞 F) F → ℂ}
    (ha : a ∈ memberSubmodule F Φ₀ ξ) (hb : b ∈ memberSubmodule F Φ₀ ξ) :
    eLpNorm (a - b) 2 (weightedMeasure F Φ₀ σ) < ⊤ :=
  (memLp_weightedMeasure_of_mem F hΦ₀ σ ((memberSubmodule F Φ₀ ξ).sub_mem ha hb)).eLpNorm_lt_top

private theorem continuous_adelicArchGLIncl' : Continuous (adelicArchGLIncl F) := by
  refine Units.continuous_iff.mpr ⟨continuous_matrix fun i j => ?_, continuous_matrix fun i j => ?_⟩
  · have : (fun k : GL (Fin 2) (InfiniteAdeleRing F) =>
        ((adelicArchGLIncl F k : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j)
        = fun k : GL (Fin 2) (InfiniteAdeleRing F) => (((k : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
            (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) : AdeleRing (𝓞 F) F) := by
      funext k; rfl
    have hc : Continuous fun k : GL (Fin 2) (InfiniteAdeleRing F) => (((k : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
        (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) : AdeleRing (𝓞 F) F) :=
      (Units.continuous_val.matrix_elem i j).prodMk continuous_const
    rw [← this] at hc
    exact hc
  · have : (fun k : GL (Fin 2) (InfiniteAdeleRing F) =>
        (((adelicArchGLIncl F k)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j)
        = fun k : GL (Fin 2) (InfiniteAdeleRing F) => ((((k⁻¹ : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
            (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) : AdeleRing (𝓞 F) F) := by
      funext k; rw [← map_inv]; rfl
    have hc : Continuous fun k : GL (Fin 2) (InfiniteAdeleRing F) =>
        ((((k⁻¹ : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
          (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) : AdeleRing (𝓞 F) F) :=
      (Units.continuous_coe_inv.matrix_elem i j).prodMk continuous_const
    rw [← this] at hc
    exact hc

open scoped Classical in
omit [NumberField F] in
private theorem continuous_archEntries [NumberField F] : Continuous (archEntries F) :=
  continuous_pi fun i => continuous_pi fun j =>
    (NumberField.AdelicBox.continuous_ringEquiv_mixedSpace F).comp (Units.continuous_val.matrix_elem i j)

open scoped Classical in
private theorem IsArchTestFactor.continuous' {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (h : IsArchTestFactor F fa) :
    Continuous fa := by
  obtain ⟨⟨Φ, hΦ, heq⟩, -⟩ := h
  have : fa = Φ ∘ archEntries F := funext heq
  rw [this]
  exact hΦ.continuous.comp continuous_archEntries

open scoped Classical in
private theorem IsArchTestFactor.const_mul' {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (h : IsArchTestFactor F fa) (c : ℂ) :
    IsArchTestFactor F (fun y => c * fa y) := by
  obtain ⟨⟨Φ, hΦ, heq⟩, hK⟩ := h
  exact ⟨⟨fun A => c * Φ A, contDiff_const.mul hΦ, fun g => by show c * fa g = c * Φ (archEntries F g); rw [heq]⟩, hK.mul_left⟩

private theorem ideleNorm_det_eq_of_glFin_mem_finiteIntegralGL2 (g : AdelicGL2 (𝓞 F) F)
    (hg : glFin (𝓞 F) F g ∈ finiteIntegralGL2 (𝓞 F) F) :
    NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g)
      = NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F (glArch (𝓞 F) F g))) := by
  rw [NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult F g hg,
    NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult F (adelicArchGLIncl F (glArch (𝓞 F) F g))
      (by rw [glFin_adelicArchGLIncl]; exact one_mem _)]
  refine Finset.prod_congr rfl fun w _ => ?_
  unfold NumberField.AdelicVolume.archDetNorm
  rw [glArch_adelicArchGLIncl]

private theorem isFinTestFactor_indicator {S : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))} (hSo : IsOpen S) (hSc : IsCompact S) :
    IsFinTestFactor F (S.indicator fun _ => (1 : ℂ)) := by
  haveI : T2Space (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) := inferInstance
  have hScl : IsClosed S := hSc.isClosed
  refine ⟨fun s => ?_, HasCompactSupport.intro hSc fun y hy => Set.indicator_of_notMem hy _⟩
  by_cases h1 : (1 : ℂ) ∈ s <;> by_cases h0 : (0 : ℂ) ∈ s
  · have : (S.indicator fun _ => (1 : ℂ)) ⁻¹' s = Set.univ := by
      ext y; by_cases hy : y ∈ S <;> simp [Set.indicator, hy, h1, h0]
    rw [this]; exact isOpen_univ
  · have : (S.indicator fun _ => (1 : ℂ)) ⁻¹' s = S := by
      ext y; by_cases hy : y ∈ S <;> simp [Set.indicator, hy, h1, h0]
    rw [this]; exact hSo
  · have : (S.indicator fun _ => (1 : ℂ)) ⁻¹' s = Sᶜ := by
      ext y; by_cases hy : y ∈ S <;> simp [Set.indicator, hy, h1, h0]
    rw [this]; exact hScl.isOpen_compl
  · have : (S.indicator fun _ => (1 : ℂ)) ⁻¹' s = ∅ := by
      ext y; by_cases hy : y ∈ S <;> simp [Set.indicator, hy, h1, h0]
    rw [this]; exact isOpen_empty

end T6Assembly

end

set_option maxHeartbeats 1600000 in
open T6Assembly in
theorem solution
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hUf : U ≤ finiteAdelicGL2Subgroup F)
    (hUo : IsOpen ((AdelicLevel.glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))))
    (hUc : IsCompact ((AdelicLevel.glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))))
    (hUi : (AdelicLevel.glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) ⊆ (finiteIntegralGL2 (𝓞 F) F : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))))
    (tys : AutomorphicForm.ArchTypeFamily F)
    (x : AdelicGL2 (𝓞 F) F → ℂ) (hx : x ∈ cuspMemberSubmodule F Φ₀ ξ)
    (hxU : ∀ g : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, x (g * u) = x g) (hxt : x ∈ archCutSubmodule F tys)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ f : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f ∧
      IsLevelSphericalOfType F tys U f ∧
      flat F σ f = f ∧
      ∃ hxf : rightConv F x f ∈ cuspMemberSubmodule F Φ₀ ξ,
        ‖toCuspSubcarrier F hΦ₀ σ ξ ⟨x, hx⟩ - toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F x f, hxf⟩‖ < ε := by
  classical

  haveI hBorelA : BorelSpace (AdelicGL2 (𝓞 F) F) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 F) F) := NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F

  haveI : ∀ w : InfinitePlace F, CompactSpace ↥(rowIsometrySubgroup₀ w.Completion) := fun w =>
    isCompact_iff_compactSpace.mp (AutomorphicForm.isCompact_rowIsometrySubgroup_detOne F w)
  haveI : CompactSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) := Pi.compactSpace
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → InfiniteAdeleRing F))
  haveI : LocallyCompactSpace (GL (Fin 2) (InfiniteAdeleRing F)) := inferInstance
  letI mK : MeasurableSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) := borel _
  haveI : BorelSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) := ⟨rfl⟩
  haveI : Nonempty (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) := ⟨1⟩
  set μK : Measure (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) with hμK
  haveI hKprob : IsProbabilityMeasure μK :=
    ⟨by rw [hμK, ← TopologicalSpace.PositiveCompacts.coe_top]; exact Measure.haarMeasure_self⟩
  haveI hKright : μK.IsMulRightInvariant := by
    refine ⟨fun g => ?_⟩
    haveI : IsProbabilityMeasure (μK.map (· * g)) := Measure.isProbabilityMeasure_map (measurable_mul_const g).aemeasurable
    exact eq_of_isMulLeftInvariant_of_isProbabilityMeasure (μK.map (· * g)) μK
  haveI hKinv : μK.IsInvInvariant := by
    refine ⟨?_⟩
    haveI : IsProbabilityMeasure μK.inv := by
      rw [Measure.inv_def]; exact Measure.isProbabilityMeasure_map measurable_inv.aemeasurable
    exact eq_of_isMulLeftInvariant_of_isProbabilityMeasure μK.inv μK

  letI mA : MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing F)) := borel _
  haveI : BorelSpace (GL (Fin 2) (InfiniteAdeleRing F)) := ⟨rfl⟩
  set μa : Measure (GL (Fin 2) (InfiniteAdeleRing F)) := Measure.haar with hμa
  haveI : μa.Regular := by rw [hμa]; infer_instance
  haveI hAright : μa.IsMulRightInvariant :=
    NumberField.AdelicHaar.isMulRightInvariant_of_isHaarMeasure_generalLinearGroup_infiniteAdeleRing F μa

  have hxc : Continuous x := hx.2
  obtain ⟨hEfd, hEc, hEt, hEK⟩ :=
    AutomorphicForm.finiteDimensional_span_translates_of_mem_archCutSubmodule F (iota F) archComponent_iota tys x hxc hxt
  set E : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := Submodule.span ℂ (Set.range fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) => fun g : AdelicGL2 (𝓞 F) F => x (g * adelicArchGLIncl F (iota F κ))) with hE
  have hxE : x ∈ E := by
    refine Submodule.subset_span ⟨1, ?_⟩
    funext g
    simp only [map_one, mul_one]
  obtain ⟨e, he, hecl, hefl, het, het', hrep⟩ :=
    AutomorphicForm.exists_continuous_conj_invariant_integral_mul_apply_mul_eq_of_finiteDimensional_of_le_archCutSubmodule
      F μK (iota F) archComponent_iota tys E hEfd hEc hEt hEK

  have hxcm : x ∈ contMemberSubmodule F Φ₀ ξ := ⟨hx.1.1.1, hx.2⟩
  obtain ⟨V, hV, hVest⟩ :=
    AutomorphicForm.CuspidalSpectrum.exists_nhds_forall_norm_toCarrier_rightTranslate_sub_lt F hΦ₀ σ ξ hσ x hxcm (ε / 2)
      (half_pos hε)
  have hinclc : Continuous (adelicArchGLIncl F) := continuous_adelicArchGLIncl'
  have hVinf : (adelicArchGLIncl F) ⁻¹' V ∈ 𝓝 (1 : GL (Fin 2) (InfiniteAdeleRing F)) := by
    refine hinclc.continuousAt.preimage_mem_nhds ?_
    rwa [map_one]
  obtain ⟨h₀, hh₀t, hh₀re, hh₀1, hh₀V, hh₀c, hh₀f⟩ :=
    AutomorphicForm.exists_isArchTestFactor_nonneg_and_tsupport_subset_and_conj_invariant_and_flat F σ _ hVinf

  have hUimg : (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) = ((U.map (glFin (𝓞 F) F) : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) :=
    (Subgroup.coe_map (glFin (𝓞 F) F) U).symm
  obtain ⟨C, hCpos, hC⟩ :=
    AutomorphicForm.exists_pos_forall_rightConv_integral_prod_mul_indicator_eq_mul_integral_of_forall_integral_mul_apply_mul_eq
      F μK (iota F) continuous_iota archComponent_iota μa U hUf hUo hUc

  set I₀ : ℝ := ∫ a, (h₀ a).re ∂μa with hI₀
  have hh₀cont : Continuous h₀ := IsArchTestFactor.continuous' hh₀t
  have hh₀K : HasCompactSupport h₀ := hh₀t.2
  have hI₀pos : 0 < I₀ := by
    have hre : Continuous fun a => (h₀ a).re := Complex.continuous_re.comp hh₀cont
    have hreK : HasCompactSupport fun a => (h₀ a).re := hh₀t.2.comp_left Complex.zero_re
    exact hre.integral_pos_of_hasCompactSupport_nonneg_nonzero hreK (fun a => (hh₀re a).2) hh₀1.ne'
  set c : ℝ := (C * I₀)⁻¹ with hc
  have hcpos : 0 < c := inv_pos.mpr (mul_pos hCpos hI₀pos)
  set h : GL (Fin 2) (InfiniteAdeleRing F) → ℂ := fun a => (c : ℂ) * h₀ a with hh
  have hht : IsArchTestFactor F h := IsArchTestFactor.const_mul' hh₀t (c : ℂ)
  have hhcont : Continuous h := continuous_const.mul hh₀cont
  have hhK : HasCompactSupport h := hh₀K.mul_left
  have hhc : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (y : GL (Fin 2) (InfiniteAdeleRing F)),
      h (archRowIsometryInclAt₀ F w k * y * (archRowIsometryInclAt₀ F w k)⁻¹) = h y := fun w k y => by
    simp only [hh, hh₀c w k y]
  have hhf : ∀ y : GL (Fin 2) (InfiniteAdeleRing F), h y = conj (h y⁻¹) *
      ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F y)) ^ (-σ) : ℝ) : ℂ) := by
    intro y
    simp only [hh, map_mul, Complex.conj_ofReal, mul_assoc]
    rw [← hh₀f y]

  set fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ := fun y => ∫ p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion),
      e p.1 * e p.2 * h ((iota F p.1)⁻¹ * y * (iota F p.2)⁻¹) ∂(μK.prod μK) with hfa
  set f : AdelicGL2 (𝓞 F) F → ℂ := fun g => fa (glArch (𝓞 F) F g) *
      Set.indicator ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ)) (glFin (𝓞 F) F g) with hfdef
  obtain ⟨hfa_t, hfa_bf⟩ :=
    AutomorphicForm.isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule
      F μK (iota F) archComponent_iota tys e e he he h hht
  have hfa_bf' : IsArchFactorBiFinite F tys fa := hfa_bf het het'
  obtain ⟨hfa_c, hfa_f⟩ :=
    AutomorphicForm.integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat
      F μK (iota F) archComponent_iota σ e hecl hefl h hhc hhf
  have hsph : IsLevelSphericalOfType F tys U f :=
    ⟨fa, hfa_t, hfa_bf', fun w k y => hfa_c w k y, fun g => rfl⟩
  have hff : IsFinTestFactor F
      (Set.indicator ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ))) :=
    isFinTestFactor_indicator hUo hUc
  have hftest : IsFactorizableTestFn F f := ⟨fa, _, hfa_t, hff, fun g => rfl⟩
  have hflat : flat F σ f = f := by
    funext g
    show conj (f g⁻¹) * ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-σ) : ℝ) : ℂ) = f g
    simp only [hfdef, map_inv]
    by_cases hg : glFin (𝓞 F) F g ∈ (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))
    · have hg' : (glFin (𝓞 F) F g)⁻¹ ∈ (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) := by
        rw [hUimg] at hg ⊢; exact inv_mem hg
      rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg', mul_one, mul_one]
      rw [ideleNorm_det_eq_of_glFin_mem_finiteIntegralGL2 g (SetLike.mem_coe.mp (hUi hg))]
      exact (hfa_f (glArch (𝓞 F) F g)).symm
    · have hg' : (glFin (𝓞 F) F g)⁻¹ ∉ (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) := by
        rw [hUimg] at hg ⊢; exact fun h => hg (by simpa using inv_mem h)
      rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg', mul_zero, mul_zero, map_zero, zero_mul]
  have hxf : rightConv F x f ∈ cuspMemberSubmodule F Φ₀ ξ :=
    AutomorphicForm.CuspidalSpectrum.rightConv_mem_cuspMemberSubmodule F hΦ₀ ξ f hftest x hx

  have hconv : ∀ g : AdelicGL2 (𝓞 F) F, rightConv F x f g = C * ∫ a, x (g * adelicArchGLIncl F a) * h a ∂μa :=
    hC e he h hhcont hhK hhc x hxc hxU (fun z => hrep x hxE z)
  set p : GL (Fin 2) (InfiniteAdeleRing F) → ℝ := fun a => (h₀ a).re / I₀ with hp
  have hconv' : ∀ g : AdelicGL2 (𝓞 F) F, rightConv F x f g = ∫ a, x (g * adelicArchGLIncl F a) * (p a : ℂ) ∂μa := by
    intro g
    rw [hconv g]
    have h1 : ∀ a, x (g * adelicArchGLIncl F a) * h a = (c : ℂ) * (x (g * adelicArchGLIncl F a) * h₀ a) := fun a => by
      simp only [hh]; ring
    have h2 : ∀ a, x (g * adelicArchGLIncl F a) * (p a : ℂ) = (x (g * adelicArchGLIncl F a) * h₀ a) * ((I₀ : ℂ))⁻¹ := by
      intro a
      simp only [hp, Complex.ofReal_div]
      rw [(hh₀re a).1]
      ring
    simp_rw [h1, h2, integral_const_mul, integral_mul_const]
    have hCc : (C : ℂ) * (c : ℂ) = ((I₀ : ℂ))⁻¹ := by
      simp only [hc, Complex.ofReal_inv, Complex.ofReal_mul]
      field_simp [Complex.ofReal_ne_zero.mpr hCpos.ne', Complex.ofReal_ne_zero.mpr hI₀pos.ne']
    rw [← mul_assoc, hCc, mul_comm]

  refine ⟨f, hftest, hsph, hflat, hxf, ?_⟩

  have hnorm : ∀ v : ↥(cuspSubcarrier F hΦ₀ σ ξ), ‖v‖ = ‖(v : Carrier F Φ₀ σ)‖ := fun v => rfl
  rw [hnorm, Submodule.coe_sub, toCuspSubcarrier_apply_coe, toCuspSubcarrier_apply_coe,
    norm_toCarrier_sub hΦ₀ σ ξ]
  set ν : Measure (AdelicGL2 (𝓞 F) F) := weightedMeasure F Φ₀ σ with hν

  have hfin := eLpNorm_sub_lt_top hΦ₀ σ hx.1.1.1 hxf.1.1.1
  suffices hmain : eLpNorm (x - rightConv F x f) 2 ν ^ 2 ≤ ENNReal.ofReal (ε / 2) ^ 2 by
    have h1 : eLpNorm (x - rightConv F x f) 2 ν ≤ ENNReal.ofReal (ε / 2) :=
      (ENNReal.pow_le_pow_left_iff two_ne_zero).mp hmain
    calc (eLpNorm (x - rightConv F x f) 2 ν).toReal ≤ ε / 2 :=
          ENNReal.toReal_le_of_le_ofReal (half_pos hε).le h1
      _ < ε := half_lt_self hε

  haveI : SigmaFinite (adelicGLHaar (Fin 2) (𝓞 F) F) := by
    haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
    infer_instance
  haveI : SFinite ν := by rw [hν, weightedMeasure]; infer_instance
  haveI : SFinite μa := by
    haveI : ∀ v : InfinitePlace F, ProperSpace v.Completion := fun v => properSpace_completion v
    haveI : SecondCountableTopology (InfiniteAdeleRing F) :=
      inferInstanceAs (SecondCountableTopology (∀ v : InfinitePlace F, v.Completion))
    haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
      inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → InfiniteAdeleRing F))
    haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))ᵐᵒᵖ :=
      MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
    haveI : SecondCountableTopology (GL (Fin 2) (InfiniteAdeleRing F)) := Units.isEmbedding_embedProduct.secondCountableTopology
    infer_instance

  have hpc : Continuous p := (Complex.continuous_re.comp hh₀cont).div_const _
  have hp0 : ∀ a, 0 ≤ p a := fun a => div_nonneg (hh₀re a).2 hI₀pos.le
  have hp1 : ∫ a, p a ∂μa = 1 := by
    simp only [hp, integral_div]
    exact div_self hI₀pos.ne'
  have hpK : HasCompactSupport p := by
    have : p = (fun r : ℝ => r / I₀) ∘ (fun a => (h₀ a).re) := rfl
    rw [this]
    exact (hh₀t.2.comp_left Complex.zero_re).comp_left (zero_div _)
  have hU : Measurable (Function.uncurry fun (g : AdelicGL2 (𝓞 F) F) (a : GL (Fin 2) (InfiniteAdeleRing F)) => x (g * adelicArchGLIncl F a)) :=
    (hxc.comp (continuous_fst.mul (hinclc.comp continuous_snd))).measurable
  have hint : ∀ g : AdelicGL2 (𝓞 F) F, Integrable (fun a => x (g * adelicArchGLIncl F a) * (p a : ℂ)) μa := fun g =>
    ((hxc.comp (continuous_const.mul hinclc)).mul (Complex.continuous_ofReal.comp hpc)).integrable_of_hasCompactSupport
      ((hpK.comp_left Complex.ofReal_zero).mul_left)
  have hJ := MeasureTheory.lintegral_enorm_sub_integral_mul_sq_le_lintegral_mul_lintegral_enorm_sub_sq ν μa p hpc.measurable
    hp0 hp1 x hxc.measurable (fun (g : AdelicGL2 (𝓞 F) F) (a : GL (Fin 2) (InfiniteAdeleRing F)) => x (g * adelicArchGLIncl F a)) hU hint

  have hL : eLpNorm (x - rightConv F x f) 2 ν ^ 2 = ∫⁻ g, ‖x g - ∫ a, x (g * adelicArchGLIncl F a) * (p a : ℂ) ∂μa‖ₑ ^ 2 ∂ν := by
    rw [eLpNorm_two_pow_two]
    refine lintegral_congr fun g => ?_
    rw [Pi.sub_apply, hconv' g]
  rw [hL]
  refine hJ.trans ?_

  have hpt : ∀ a, p a ≠ 0 → adelicArchGLIncl F a ∈ V := by
    intro a ha
    have : a ∈ tsupport h₀ := by
      refine subset_tsupport _ ?_
      intro h0; apply ha; simp only [hp, h0, Complex.zero_re, zero_div]
    exact hh₀V this
  have hB : ∀ a, ENNReal.ofReal (p a) * ∫⁻ g, ‖x g - x (g * adelicArchGLIncl F a)‖ₑ ^ 2 ∂ν
      ≤ ENNReal.ofReal (p a) * ENNReal.ofReal (ε / 2) ^ 2 := by
    intro a
    by_cases ha : p a = 0
    · simp [ha]
    obtain ⟨hy, hlt⟩ := hVest _ (hpt a ha)
    refine mul_le_mul_right ?_ _
    have heq : ∫⁻ g, ‖x g - x (g * adelicArchGLIncl F a)‖ₑ ^ 2 ∂ν
        = eLpNorm (rightTranslate F (adelicArchGLIncl F a) x - x) 2 ν ^ 2 := by
      rw [eLpNorm_two_pow_two]
      refine lintegral_congr fun g => ?_
      rw [Pi.sub_apply, rightTranslate_apply, enorm_sub_rev]
    rw [heq]
    have hlt' : eLpNorm (rightTranslate F (adelicArchGLIncl F a) x - x) 2 ν < ENNReal.ofReal (ε / 2) := by
      rw [norm_toCarrier_sub hΦ₀ σ ξ] at hlt
      exact (ENNReal.lt_ofReal_iff_toReal_lt (eLpNorm_sub_lt_top hΦ₀ σ hy.1 hx.1.1.1).ne).mpr hlt
    exact pow_le_pow_left' hlt'.le 2
  calc ∫⁻ a, ENNReal.ofReal (p a) * ∫⁻ g, ‖x g - x (g * adelicArchGLIncl F a)‖ₑ ^ 2 ∂ν ∂μa
      ≤ ∫⁻ a, ENNReal.ofReal (p a) * ENNReal.ofReal (ε / 2) ^ 2 ∂μa := lintegral_mono hB
    _ = (∫⁻ a, ENNReal.ofReal (p a) ∂μa) * ENNReal.ofReal (ε / 2) ^ 2 := by
        rw [lintegral_mul_const _ hpc.measurable.ennreal_ofReal]
    _ = ENNReal.ofReal (ε / 2) ^ 2 := by
        rw [← ofReal_integral_eq_lintegral_ofReal (hpc.integrable_of_hasCompactSupport hpK) (ae_of_all _ hp0), hp1,
          ENNReal.ofReal_one, one_mul]

end S_AutomorphicForm_CuspidalSpectrum_exists_isLevelSphericalOfType_flat_norm_toCuspSubcarrier_sub_lt_of_forall_apply_mul_eq
end P2MW
export P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_isLevelSphericalOfType_flat_norm_toCuspSubcarrier_sub_lt_of_forall_apply_mul_eq (solution)
