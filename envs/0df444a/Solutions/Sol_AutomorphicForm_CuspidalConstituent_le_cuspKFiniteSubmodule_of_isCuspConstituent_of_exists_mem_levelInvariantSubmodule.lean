-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.le_cuspKFiniteSubmodule_of_isCuspConstituent_of_exists_mem_levelInvariantSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/992a1dbe-5c12-5614-beb2-2b7804a467a8

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
import Definitions.Def_NumberField_SiegelVolume
import Theorems.Thm_AutomorphicForm_rightConv_mem_archCutSubmodule_of_isArchBiFinite
import Theorems.Thm_AutomorphicForm_exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCuspidalFn_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_rightTranslate_mem_cuspMemberSubmodule
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_rightConv_mem_cuspMemberSubmodule
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isSlabFundamentalDomain
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_cuspKFiniteSubmodule_le_cuspMemberSubmodule
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_rightConv_injOn_of_finiteDimensional_of_le
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_hasModulus_of_isCuspConstituent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_le_cuspKFiniteSubmodule_of_isCuspConstituent_of_exists_mem_levelInvariantSubmodule
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"
p2m_attr_erase "simp" "AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed"

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_CuspidalConstituent_le_cuspKFiniteSubmodule_of_isCuspConstituent_of_exists_mem_levelInvariantSubmodule.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering"
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "comp_mul_mem_typeSubmodule_of_commute ArchRepAt rowIsometryInclAt₀ archTypeSubmoduleAt ArchTypeFamily archCutSubmodule mem_archCutSubmodule_iff archCutSubmodule_mono IsArchBiFinite glFin_rowIsometryInclAt₀ IsArchBiFinite.of_factorization CarrierPins productionPinsOf AdelicGL2 finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff lsXiMemberAt_iff rightConv rowIsometrySubgroup₀ IsFactorizableTestFn rightConv_mem_archCutSubmodule_of_isArchBiFinite exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCuspidalFn_of_isFundamentalDomain CuspidalSpectrum.rightTranslate_mem_cuspMemberSubmodule CuspidalSpectrum.rightConv_mem_cuspMemberSubmodule CuspidalSpectrum.exists_isSlabFundamentalDomain CuspidalSpectrum.cuspKFiniteSubmodule_le_cuspMemberSubmodule CuspidalConstituent.continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule CuspidalConstituent.exists_rightConv_injOn_of_finiteDimensional_of_le CuspidalSpectrum.exists_hasModulus_of_isCuspConstituent"
namespace CutWindowTransfer
p2m_open "AutomorphicForm"

variable {F : Type} [Field F] [NumberField F]

def appendFam (tys tys' : ArchTypeFamily F) : ArchTypeFamily F where
  card w := tys.card w + tys'.card w
  rep w := Fin.addCases (tys.rep w) (tys'.rep w)

omit [NumberField F] in
theorem isContainedIn_appendFam_left (tys tys' : ArchTypeFamily F) : tys.IsContainedIn F (appendFam tys tys') :=
  fun w i => ⟨Fin.castAdd (tys'.card w) i, Fin.addCases_left (motive := fun _ => ArchRepAt F w) i⟩

omit [NumberField F] in
theorem isContainedIn_appendFam_right (tys tys' : ArchTypeFamily F) : tys'.IsContainedIn F (appendFam tys tys') :=
  fun w i => ⟨Fin.natAdd (tys.card w) i, Fin.addCases_right (motive := fun _ => ArchRepAt F w) i⟩

theorem exists_mem_archCutSubmodule_of_mem_cuspKFiniteSubmodule (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ cuspKFiniteSubmodule F pins ξ) :
    ∃ tys : ArchTypeFamily F, φ ∈ archCutSubmodule F tys := by
  refine Submodule.span_induction (p := fun φ _ => ∃ tys : ArchTypeFamily F, φ ∈ archCutSubmodule F tys)
    ?_ ?_ ?_ ?_ hφ
  · rintro φ ⟨-, -, tys, htys⟩
    exact ⟨tys, htys⟩
  · exact ⟨⟨fun _ => 0, fun _ i => i.elim0⟩, Submodule.zero_mem _⟩
  · rintro a b - - ⟨ta, ha⟩ ⟨tb, hb⟩
    exact ⟨appendFam ta tb, Submodule.add_mem _
      (archCutSubmodule_mono F (isContainedIn_appendFam_left ta tb) ha)
      (archCutSubmodule_mono F (isContainedIn_appendFam_right ta tb) hb)⟩
  · rintro c a - ⟨t, h⟩
    exact ⟨t, Submodule.smul_mem _ c h⟩

theorem commute_rowIsometryInclAt₀_of_mem_finiteAdelicGL2Subgroup
    {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ finiteAdelicGL2Subgroup F)
    (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    Commute g (rowIsometryInclAt₀ F w k) := by
  have hg1 : glArch (𝓞 F) F g = 1 := (mem_finiteAdelicGL2Subgroup_iff F g).mp hg
  have h1 : glArch (𝓞 F) F (g * rowIsometryInclAt₀ F w k) = glArch (𝓞 F) F (rowIsometryInclAt₀ F w k * g) := by
    rw [map_mul, map_mul, hg1, one_mul, mul_one]
  have h2 : glFin (𝓞 F) F (g * rowIsometryInclAt₀ F w k) = glFin (𝓞 F) F (rowIsometryInclAt₀ F w k * g) := by
    rw [map_mul, map_mul, glFin_rowIsometryInclAt₀, one_mul, mul_one]
  show g * rowIsometryInclAt₀ F w k = rowIsometryInclAt₀ F w k * g
  refine Units.ext (Matrix.ext fun i j => Prod.ext ?_ ?_)
  · have := congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing F) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) h1
    simpa only [glArch_apply] using this
  · have := congrArg (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) =>
      (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) h2
    simpa only [glFin_apply] using this

theorem rightTranslate_mem_archCutSubmodule_of_mem_finiteAdelicGL2Subgroup (tys : ArchTypeFamily F)
    {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ finiteAdelicGL2Subgroup F)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ archCutSubmodule F tys) :
    rightTranslate F g φ ∈ archCutSubmodule F tys := by
  rw [mem_archCutSubmodule_iff] at hφ ⊢
  intro w
  have key : ∀ i : Fin (tys.card w),
      (archTypeSubmoduleAt F w (tys.rep w i)).map (rightRegular F g) ≤ archTypeSubmoduleAt F w (tys.rep w i) := by
    intro i f hf
    obtain ⟨f₀, hf₀, rfl⟩ := Submodule.mem_map.mp hf
    exact comp_mul_mem_typeSubmodule_of_commute hf₀ _
      fun k => commute_rowIsometryInclAt₀_of_mem_finiteAdelicGL2Subgroup hg w k
  have hmap : (⨆ i, archTypeSubmoduleAt F w (tys.rep w i)).map (rightRegular F g)
      ≤ ⨆ i, archTypeSubmoduleAt F w (tys.rep w i) := by
    rw [Submodule.map_iSup]; exact iSup_mono key
  exact hmap (Submodule.mem_map_of_mem (hφ w))

theorem rightTranslate_mem_cuspKFiniteSubmodule_of_mem_finiteAdelicGL2Subgroup
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ξ : (productionPinsOf F D U gen (adelicBox F)).Z →* ℂˣ)
    {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ finiteAdelicGL2Subgroup F)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ cuspKFiniteSubmodule F (productionPinsOf F D U gen (adelicBox F)) ξ) :
    rightTranslate F g φ ∈ cuspKFiniteSubmodule F (productionPinsOf F D U gen (adelicBox F)) ξ := by
  refine Submodule.span_induction
    (p := fun φ _ => rightTranslate F g φ ∈ cuspKFiniteSubmodule F (productionPinsOf F D U gen (adelicBox F)) ξ)
    ?_ ?_ ?_ ?_ hφ
  · rintro φ ⟨hsat, hcont, tys, htys⟩
    exact Submodule.subset_span ⟨forall_isSmoothCuspAutomorphicFnAt_rightTranslate_rightTranslate F hsat _,
      continuous_rightTranslate F hcont _, tys,
      rightTranslate_mem_archCutSubmodule_of_mem_finiteAdelicGL2Subgroup tys hg htys⟩
  · show rightTranslate F _ 0 ∈ _
    rw [rightTranslate_zero]; exact (cuspKFiniteSubmodule F _ ξ).zero_mem
  · intro a b _ _ ha hb
    show rightTranslate F _ (a + b) ∈ _
    rw [rightTranslate_add]; exact (cuspKFiniteSubmodule F _ ξ).add_mem ha hb
  · intro c a _ ha
    show rightTranslate F _ (c • a) ∈ _
    rw [rightTranslate_smul]; exact (cuspKFiniteSubmodule F _ ξ).smul_mem c ha

theorem rightConv_mem_cuspKFiniteSubmodule_of_mem_cuspMemberSubmodule
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (c' u' d₁' d₂' : ℝ) (T' : Finset (AdelicGL2 (𝓞 F) F)) (hc' : 0 < c') (hd₁' : 0 < d₁')
    (tys : ArchTypeFamily F) (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) (hft : IsArchBiFinite F tys f)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ) :
    rightConv F φ f ∈ cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T', (· * x) '' centreCutSiegelSet F c' u' d₁' d₂')
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ := by
  classical
  set ψ : AdelicGL2 (𝓞 F) F → ℂ := rightConv F φ f with hψdef
  have hψ : ψ ∈ cuspMemberSubmodule F Φ₀ ξ :=
    AutomorphicForm.CuspidalSpectrum.rightConv_mem_cuspMemberSubmodule F hΦ₀ ξ f hf φ hφ
  have hcont : Continuous ψ := hψ.2
  have hcut : ψ ∈ archCutSubmodule F tys :=
    AutomorphicForm.rightConv_mem_archCutSubmodule_of_isArchBiFinite F tys φ hφ.2 f hf hft
  refine Submodule.subset_span ⟨fun g => ?_, hcont, tys, hcut⟩

  have hy : rightTranslate F g ψ ∈ cuspMemberSubmodule F Φ₀ ξ :=
    AutomorphicForm.CuspidalSpectrum.rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ g ψ hψ
  have hlx := (mem_memberSubmodule_iff' F Φ₀ ξ φ).mp hφ.1.1.1
  have hlxy := (mem_memberSubmodule_iff' F Φ₀ ξ (rightTranslate F g ψ)).mp hy.1.1.1

  have hMemD : MemLp (rightTranslate F g ψ) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T', (· * x) '' centreCutSiegelSet F c' u' d₁' d₂')) := by
    haveI hRinv : (adelicGLHaar (Fin 2) (𝓞 F) F).IsMulRightInvariant :=
      NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar F
    have hDclosed : IsClosed (⋃ x ∈ T', (· * x) '' centreCutSiegelSet F c' u' d₁' d₂') := by
      refine Set.Finite.isClosed_biUnion (Finset.finite_toSet T') fun x _ => ?_
      exact (Homeomorph.mulRight x).isClosed_image.mpr (isClosed_centreCutSiegelSet c' u' d₁' d₂')
    have hDfin : adelicGLHaar (Fin 2) (𝓞 F) F (⋃ x ∈ T', (· * x) '' centreCutSiegelSet F c' u' d₁' d₂') < ⊤ := by
      refine (measure_biUnion_finset_le T' _).trans_lt (ENNReal.sum_lt_top.mpr fun x _ => ?_)
      have himg : (· * x) '' centreCutSiegelSet F c' u' d₁' d₂' = (· * x⁻¹) ⁻¹' centreCutSiegelSet F c' u' d₁' d₂' := by
        ext g'; constructor
        · rintro ⟨h, hh, rfl⟩; simpa [mul_inv_cancel_right] using hh
        · intro hg; exact ⟨g' * x⁻¹, hg, by simp only [inv_mul_cancel_right]⟩
      rw [himg, ← Measure.map_apply (measurable_mul_const x⁻¹) (isClosed_centreCutSiegelSet c' u' d₁' d₂').measurableSet,
        map_mul_right_eq_self]
      exact NumberField.SiegelVolume.measure_centreCutSiegelSet_lt_top (F := F) (adelicGLHaar (Fin 2) (𝓞 F) F) hc' u' hd₁' d₂'
    haveI : IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T', (· * x) '' centreCutSiegelSet F c' u' d₁' d₂')) :=
      isFiniteMeasure_restrict.mpr hDfin.ne

    obtain ⟨C, hC⟩ :=
      AutomorphicForm.exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCuspidalFn_of_isFundamentalDomain
        F ξ f hf c' u' d₁' d₂' (T'.image (· * g)) hc' hd₁' α β hΦ₀.pos_right hΦ₀.lt Φ₀ hΦ₀.isFundamentalDomain
    have hb := hC φ hlx.1 hφ.1.1.2 hφ.2 hlx.2
    refine MemLp.of_bound hy.2.aestronglyMeasurable
      (C * (eLpNorm φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀)).toReal)
      ((ae_restrict_mem hDclosed.measurableSet).mono fun y hyW => ?_)
    obtain ⟨x, hx, s, hs, rfl⟩ := Set.mem_iUnion₂.mp hyW
    have hmemg : s * x * g ∈ ⋃ x' ∈ T'.image (· * g), (· * x') '' centreCutSiegelSet F c' u' d₁' d₂' :=
      Set.mem_iUnion₂.mpr ⟨x * g, Finset.mem_image_of_mem _ hx, s, hs, (mul_assoc s x g).symm⟩
    calc ‖rightTranslate F g ψ (s * x)‖ = ‖rightConv F φ f (s * x * g)‖ := by rw [rightTranslate_apply]
      _ ≤ C * (eLpNorm φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀)).toReal := hb _ hmemg
  refine ⟨⟨?_, hy.1.1.2⟩, hy.1.2⟩
  exact (lsXiMemberAt_iff (𝓞 F) F (adelicGLHaar (Fin 2) (𝓞 F) F) ⊤ ξ (⋃ x ∈ T', (· * x) '' centreCutSiegelSet F c' u' d₁' d₂') (rightTranslate F g ψ)).mpr ⟨hlxy.1, hMemD⟩

end AutomorphicForm.CutWindowTransfer

end

open AutomorphicForm.CutWindowTransfer in
theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV : IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ V)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (hVN : ∃ φ ∈ V, φ ≠ 0 ∧ φ ∈ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N)
    (c' u' d₁' d₂' : ℝ) (T' : Finset (AdelicGL2 (𝓞 F) F)) (hc' : 0 < c') (hd₁' : 0 < d₁') :
    V ≤ cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T', (· * x) '' centreCutSiegelSet F c' u' d₁' d₂')
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ := by
  classical
  obtain ⟨hVsub, hVne, hVmin⟩ := hV
  obtain ⟨φ₀, hφ₀V, hφ₀ne, hφ₀N⟩ := hVN
  set V' : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := V ⊓ cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T', (· * x) '' centreCutSiegelSet F c' u' d₁' d₂')
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ with hV'

  obtain ⟨α, β, Φ₀, hΦ₀⟩ := AutomorphicForm.CuspidalSpectrum.exists_isSlabFundamentalDomain F
  have hVmem : ∀ φ ∈ V, φ ∈ cuspMemberSubmodule F Φ₀ ξ := fun φ h =>
    AutomorphicForm.CuspidalSpectrum.cuspKFiniteSubmodule_le_cuspMemberSubmodule F c u d₁ d₂ T hc hd₁ hd hcov ξ hΦ₀ (hVsub.le h)
  have ha3 : ∀ (f : AdelicGL2 (𝓞 F) F → ℂ) (tys : ArchTypeFamily F), IsFactorizableTestFn F f → IsArchBiFinite F tys f →
      ∀ φ ∈ V', rightConv F φ f ∈ cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T', (· * x) '' centreCutSiegelSet F c' u' d₁' d₂')
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ := fun f tys hf hft φ hφ =>
    rightConv_mem_cuspKFiniteSubmodule_of_mem_cuspMemberSubmodule hΦ₀ ξ c' u' d₁' d₂' T' hc' hd₁' tys f hf hft φ (hVmem φ hφ.1)
  have hV'sub : IsCuspSubrep F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ V' := by
    refine ⟨inf_le_left.trans hVsub.le, fun g hg φ hφ => ?_, fun w k φ hφ => ?_, fun f tys hf hft φ hφ => ?_⟩
    · exact ⟨hVsub.rightTranslate_fin_mem g hg φ hφ.1,
        rightTranslate_mem_cuspKFiniteSubmodule_of_mem_finiteAdelicGL2Subgroup
          (⋃ x ∈ T', (· * x) '' centreCutSiegelSet F c' u' d₁' d₂')
          (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) ξ hg hφ.2⟩
    · exact ⟨hVsub.rightTranslate_arch_mem w k φ hφ.1,
        rightTranslate_rowIsometryInclAt₀_mem_cuspKFiniteSubmodule F
          (productionPinsOf F (⋃ x ∈ T', (· * x) '' centreCutSiegelSet F c' u' d₁' d₂')
            (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
          ξ hφ.2 w k⟩
    · exact ⟨hVsub.rightConv_mem f tys hf hft φ hφ.1, ha3 f tys hf hft φ hφ⟩

  have hV'ne : V' ≠ ⊥ := by

    obtain ⟨hφ₀c, -⟩ :=
      AutomorphicForm.CuspidalConstituent.continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule
        F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) ξ φ₀ (hVsub.le hφ₀V)
    obtain ⟨tys₀, hφ₀t⟩ := exists_mem_archCutSubmodule_of_mem_cuspKFiniteSubmodule _ ξ (hVsub.le hφ₀V)
    obtain ⟨σ, hσ⟩ := AutomorphicForm.CuspidalSpectrum.exists_hasModulus_of_isCuspConstituent F c u d₁ d₂ T ξ V ⟨hVsub, hVne, hVmin⟩

    set Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := Submodule.span ℂ ({φ₀} : Set (AdelicGL2 (𝓞 F) F → ℂ)) with hY
    have hYfd : FiniteDimensional ℂ ↥Y := FiniteDimensional.span_of_finite ℂ (Set.finite_singleton _)
    have hYc : ∀ y ∈ Y, Continuous y := by
      intro y hy
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
      exact hφ₀c.const_smul a
    have hYU : Y ≤ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N :=
      Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hφ₀N)
    have hYt : Y ≤ archCutSubmodule F tys₀ := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hφ₀t)
    obtain ⟨f, hf, hsph, -, hinj⟩ :=
      AutomorphicForm.CuspidalConstituent.exists_rightConv_injOn_of_finiteDimensional_of_le
        F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) N hN tys₀ σ Y hYfd hYc hYU hYt
    obtain ⟨fa, -, hfabf, -, hfeq⟩ := hsph
    have hft : IsArchBiFinite F tys₀ f := IsArchBiFinite.of_factorization F hfeq hfabf

    have hmem : rightConv F φ₀ f ∈ V' :=
      ⟨hVsub.rightConv_mem f tys₀ hf hft φ₀ hφ₀V,
        rightConv_mem_cuspKFiniteSubmodule_of_mem_cuspMemberSubmodule hΦ₀ ξ c' u' d₁' d₂' T' hc' hd₁' tys₀ f hf hft φ₀
          (hVmem φ₀ hφ₀V)⟩
    intro hbot
    have h0 : rightConv F φ₀ f = 0 := by
      rw [hbot] at hmem
      exact (Submodule.mem_bot ℂ).mp hmem
    exact hφ₀ne (hinj φ₀ (Submodule.subset_span rfl) h0)

  rcases hVmin V' hV'sub inf_le_left with h | h
  · exact absurd h hV'ne
  · intro φ hφ
    have : φ ∈ V' := h.symm ▸ hφ
    exact this.2

#print axioms solution

end S_AutomorphicForm_CuspidalConstituent_le_cuspKFiniteSubmodule_of_isCuspConstituent_of_exists_mem_levelInvariantSubmodule
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_le_cuspKFiniteSubmodule_of_isCuspConstituent_of_exists_mem_levelInvariantSubmodule (solution)
