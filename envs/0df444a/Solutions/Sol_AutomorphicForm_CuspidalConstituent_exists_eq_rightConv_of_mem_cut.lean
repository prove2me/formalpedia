-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.exists_eq_rightConv_of_mem_cut
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/351f0823-337f-51b0-a1fa-7030ad891c9c

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_ArchSpherical
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Theorems.Thm_AutomorphicForm_finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_rightConv_injOn_of_finiteDimensional_of_le
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_rightConv_mem_levelInvariantSubmodule_inf_archCutSubmodule_of_isArchBiFinite
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_exists_eq_rightConv_of_mem_cut
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply"
p2m_attr_erase "simp" "NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_CuspidalConstituent_exists_eq_rightConv_of_mem_cut.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain"
p2m_open "AutomorphicForm.CuspidalConstituent P2MW.S_AutomorphicForm_CuspidalConstituent_exists_eq_rightConv_of_mem_cut.AutomorphicForm.CuspidalConstituent"

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "productionPinsOf AdelicGL2 finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff rightConv_add_left ArchTypeFamily archCutSubmodule IsArchBiFinite IsArchBiFinite.of_factorization rightConv rightConv_apply IsFactorizableTestFn IsLevelSphericalOfType finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent continuous_and_hasCompactSupport_of_isFactorizableTestFn"
namespace CuspidalConstituent
p2m_export "AutomorphicForm.CuspidalConstituent" "IsCuspConstituent levelInvariantSubmodule exists_rightConv_injOn_of_finiteDimensional_of_le rightConv_mem_levelInvariantSubmodule_inf_archCutSubmodule_of_isArchBiFinite continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule"
namespace Surj
p2m_open "AutomorphicForm.CuspidalConstituent AutomorphicForm"

private theorem rightConv_smul_left (K : Type) [Field K] [NumberField K] (r : ℂ)
    (y f : AdelicGL2 (𝓞 K) K → ℂ) : rightConv K (r • y) f = r • rightConv K y f := by
  funext g
  rw [rightConv_apply, Pi.smul_apply, rightConv_apply, smul_eq_mul, ← MeasureTheory.integral_const_mul]
  congr 1
  funext z
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

private theorem levelSpherical_props (K : Type) [Field K] [NumberField K] (tys : ArchTypeFamily K)
    (U : Subgroup (AdelicGL2 (𝓞 K) K)) (hU : U ≤ finiteAdelicGL2Subgroup K)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : IsLevelSphericalOfType K tys U f) :
    IsArchBiFinite K tys f ∧
    (∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ U, f (k * g) = f g ∧ f (g * k) = f g) ∧
    (∀ x, f x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K a = 1 ∧ k ∈ U ∧ x = a * k) := by
  classical
  obtain ⟨fa, hfaT, hfabf, -, hfeq⟩ := hf
  have hS : (glFin (𝓞 K) K) '' (U : Set (AdelicGL2 (𝓞 K) K)) = ((U.map (glFin (𝓞 K) K) : Subgroup _) : Set _) :=
    (Subgroup.coe_map _ _).symm
  refine ⟨IsArchBiFinite.of_factorization K hfeq hfabf, ?_, ?_⟩
  · intro g k hk
    have hka : glArch (𝓞 K) K k = 1 := (mem_finiteAdelicGL2Subgroup_iff K k).mp (hU hk)
    have hkf : glFin (𝓞 K) K k ∈ U.map (glFin (𝓞 K) K) := Subgroup.mem_map_of_mem _ hk
    have hleft : glFin (𝓞 K) K (k * g) ∈ (glFin (𝓞 K) K) '' (U : Set (AdelicGL2 (𝓞 K) K)) ↔
        glFin (𝓞 K) K g ∈ (glFin (𝓞 K) K) '' (U : Set (AdelicGL2 (𝓞 K) K)) := by
      rw [hS, map_mul, SetLike.mem_coe, SetLike.mem_coe, Subgroup.mul_mem_cancel_left _ hkf]
    have hright : glFin (𝓞 K) K (g * k) ∈ (glFin (𝓞 K) K) '' (U : Set (AdelicGL2 (𝓞 K) K)) ↔
        glFin (𝓞 K) K g ∈ (glFin (𝓞 K) K) '' (U : Set (AdelicGL2 (𝓞 K) K)) := by
      rw [hS, map_mul, SetLike.mem_coe, SetLike.mem_coe, Subgroup.mul_mem_cancel_right _ hkf]
    constructor
    · rw [hfeq, hfeq, map_mul, hka, one_mul]
      congr 1
      simp only [Set.indicator_apply, hleft]
    · rw [hfeq, hfeq, map_mul, hka, mul_one]
      congr 1
      simp only [Set.indicator_apply, hright]
  · intro x hx
    rw [hfeq] at hx
    have hmem : glFin (𝓞 K) K x ∈ (glFin (𝓞 K) K) '' (U : Set (AdelicGL2 (𝓞 K) K)) := by
      by_contra h
      exact hx (by rw [Set.indicator_of_notMem h, mul_zero])
    obtain ⟨k, hk, hkx⟩ := hmem
    refine ⟨x * k⁻¹, k, ?_, hk, by rw [inv_mul_cancel_right]⟩
    rw [map_mul, map_inv, hkx, mul_inv_cancel]

private theorem main
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (_hc : 0 < c) (_hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily K)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hx : x ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys) :
    ∃ x' : AdelicGL2 (𝓞 K) K → ℂ, x' ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys ∧
    ∃ α : AdelicGL2 (𝓞 K) K → ℂ, IsFactorizableTestFn K α ∧ IsArchBiFinite K tys α ∧
      (∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K), α (k * g) = α g ∧ α (g * k) = α g) ∧
      x = rightConv K x' α := by
  classical

  haveI hfin : FiniteDimensional ℂ ↥(V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys) :=
    finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent K c u d₁ d₂ T hd hcov ξ N hN tys V hV

  have hXV : ∀ y, y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys → y ∈ V :=
    fun y hy => (Submodule.mem_inf.mp (Submodule.mem_inf.mp hy).1).1
  have hXlev : ∀ y, y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys →
      y ∈ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N :=
    fun y hy => (Submodule.mem_inf.mp (Submodule.mem_inf.mp hy).1).2
  have hXarch : ∀ y, y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys → y ∈ archCutSubmodule K tys :=
    fun y hy => (Submodule.mem_inf.mp hy).2
  have hXcont : ∀ y, y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys → Continuous y := fun y hy =>
    (continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule K _ _ _ ξ y
      (hV.1.le (hXV y hy))).1

  obtain ⟨f, hfT, hsph, -, hinj⟩ :=
    exists_rightConv_injOn_of_finiteDimensional_of_le K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) N hN tys 0
      (V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys) hfin hXcont
      (fun y hy => hXlev y hy) (fun y hy => hXarch y hy)
  obtain ⟨hbif, hbi, hsupp⟩ := levelSpherical_props K tys (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
    inf_le_right f hsph
  have hφc : Continuous f ∧ HasCompactSupport f := continuous_and_hasCompactSupport_of_isFactorizableTestFn K f hfT

  have hmaps : ∀ y, y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys →
      rightConv K y f ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys := by
    intro y hy
    have h1 : rightConv K y f ∈ V := hV.1.rightConv_mem f tys hfT hbif y (hXV y hy)
    have h2 := rightConv_mem_levelInvariantSubmodule_inf_archCutSubmodule_of_isArchBiFinite K
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) N tys f hfT hbif hsupp y (hXcont y hy) (hXlev y hy)
    exact Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨h1, (Submodule.mem_inf.mp h2).1⟩, (Submodule.mem_inf.mp h2).2⟩

  let Tf : ↥(V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys) →ₗ[ℂ]
      ↥(V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys) :=
    { toFun := fun y => ⟨rightConv K y f, hmaps y y.2⟩
      map_add' := fun y z => Subtype.ext (by
        show rightConv K ((y : AdelicGL2 (𝓞 K) K → ℂ) + z) f = rightConv K y f + rightConv K z f
        exact rightConv_add_left (K := K) (hXcont _ y.2) (hXcont _ z.2) hφc.1 hφc.2)
      map_smul' := fun r y => Subtype.ext (by
        show rightConv K (r • (y : AdelicGL2 (𝓞 K) K → ℂ)) f = r • rightConv K y f
        exact rightConv_smul_left K r y f) }
  have hinjT : Function.Injective Tf := by
    intro y z hyz
    have h0 : Tf (y - z) = 0 := by rw [map_sub, hyz, sub_self]
    have h1 : rightConv K ((y - z : ↥(V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys)) :
        AdelicGL2 (𝓞 K) K → ℂ) f = 0 := congrArg Subtype.val h0
    have h2 := hinj _ (y - z).2 h1
    exact sub_eq_zero.mp (Subtype.ext h2)
  have hsurj : Function.Surjective Tf := LinearMap.injective_iff_surjective.mp hinjT
  obtain ⟨x', hx'⟩ := hsurj ⟨x, hx⟩
  refine ⟨x', x'.2, f, hfT, hbif, hbi, ?_⟩
  exact (congrArg Subtype.val hx').symm

end AutomorphicForm.CuspidalConstituent.Surj

end

theorem solution
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily K)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hx : x ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys) :
    ∃ x' : AdelicGL2 (𝓞 K) K → ℂ, x' ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys ∧
    ∃ α : AdelicGL2 (𝓞 K) K → ℂ, IsFactorizableTestFn K α ∧ IsArchBiFinite K tys α ∧
      (∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K), α (k * g) = α g ∧ α (g * k) = α g) ∧
      x = rightConv K x' α :=
  AutomorphicForm.CuspidalConstituent.Surj.main K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV N hN tys x hx

end S_AutomorphicForm_CuspidalConstituent_exists_eq_rightConv_of_mem_cut
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_exists_eq_rightConv_of_mem_cut (solution)
