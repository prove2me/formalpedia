-- Prove2me | solution 1 for AutomorphicForm.isIsotypicCuspFormAt_rightConv_of_isFactorizableTestFn_of_support_subset_of_coversModCentre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/32952529-8ec9-54e0-a546-0ba65bdb692c

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_AutomorphicForm_isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset
import Theorems.Thm_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_exists_forall_norm_rightConv_le_mul_eLpNorm_of_isSmoothCuspAutomorphicFnAt_of_coversModCentre
import Theorems.Thm_AutomorphicForm_isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_coversModCentre
import Theorems.Thm_AutomorphicForm_not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre
import Theorems.Thm_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isIsotypicCuspFormAt_rightConv_of_isFactorizableTestFn_of_support_subset_of_coversModCentre
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume

noncomputable section

section ModShells

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume NumberField.AdelicVolume
open scoped ENNReal

namespace SmwShell

variable (F : Type) [Field F] [NumberField F]

private theorem memLp_two_restrict_of_bound (D : Set (AdelicGL2 (𝓞 F) F))
    (hD : adelicGLHaar (Fin 2) (𝓞 F) F D < ⊤)
    (v : AdelicGL2 (𝓞 F) F → ℂ) (hv : Continuous v) (C : ℝ) (hC : ∀ g ∈ D, ‖v g‖ ≤ C) :
    letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
    MemLp v 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict D) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict D) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hD⟩
  refine MemLp.of_bound hv.aestronglyMeasurable C ?_
  rw [ae_restrict_iff (isClosed_le hv.norm continuous_const).measurableSet]
  exact ae_of_all _ hC

private theorem rightConv_mul_left_of_forall {φ f : AdelicGL2 (𝓞 F) F → ℂ} {h : AdelicGL2 (𝓞 F) F}
    (hφ : ∀ x, φ (h * x) = φ x) (g : AdelicGL2 (𝓞 F) F) :
    rightConv F φ f (h * g) = rightConv F φ f g := by
  rw [← rightConv_comp_mul_left]
  simp only [hφ]

private theorem rightConv_mul_left_of_forall_mul {φ f : AdelicGL2 (𝓞 F) F → ℂ} {h : AdelicGL2 (𝓞 F) F}
    {c : ℂ} (hφ : ∀ x, φ (h * x) = c * φ x) (g : AdelicGL2 (𝓞 F) F) :
    rightConv F φ f (h * g) = c * rightConv F φ f g := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  rw [← rightConv_comp_mul_left, rightConv_apply, rightConv_apply]
  simp only [hφ, mul_assoc]
  exact MeasureTheory.integral_const_mul _ _

private theorem isLsXiFunction_rightConv_of_isLsXiFunction (Z : Subgroup (AdeleRing (𝓞 F) F)ˣ) (ξ : Z →* ℂˣ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsLsXiFunction (𝓞 F) F Z ξ φ) (f : AdelicGL2 (𝓞 F) F → ℂ) :
    IsLsXiFunction (𝓞 F) F Z ξ (rightConv F φ f) where
  left_invariant γ g := rightConv_mul_left_of_forall F (fun x => hφ.left_invariant γ x) g
  central_transform z g := rightConv_mul_left_of_forall_mul F (fun x => hφ.central_transform z x) g

private theorem lintegral_enorm_sq_lt_top_of_memLp (D : Set (AdelicGL2 (𝓞 F) F)) (ψ : AdelicGL2 (𝓞 F) F → ℂ)
    (h : letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
      MemLp ψ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict D)) :
    letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
    ∫⁻ g in D, ‖ψ g‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ⊤ := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  have h2 := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (f := ψ)
    (μ := (adelicGLHaar (Fin 2) (𝓞 F) F).restrict D) two_ne_zero ENNReal.ofNat_ne_top).mp h.2
  simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using h2

private theorem memLp_of_lintegral_enorm_sq_lt_top (D : Set (AdelicGL2 (𝓞 F) F)) (ψ : AdelicGL2 (𝓞 F) F → ℂ)
    (hψ : Continuous ψ)
    (h : letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
      ∫⁻ g in D, ‖ψ g‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ⊤) :
    letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
    MemLp ψ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict D) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  refine ⟨hψ.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
  simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using h

private theorem measure_window_inter_support_pos [Countable F] (c u d₁ d₂ : ℝ)
    (T : Finset (AdelicGL2 (𝓞 F) F)) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Z : Subgroup (AdeleRing (𝓞 F) F)ˣ) (ξ : Z →* ℂˣ) (hZ : ∀ z, z ∈ Z)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsLsXiFunction (𝓞 F) F Z ξ φ) (hcont : Continuous φ)
    (hne : ∃ g, φ g ≠ 0) :
    letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
    0 < adelicGLHaar (Fin 2) (𝓞 F) F
      ((⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) ∩ {g | φ g ≠ 0}) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  haveI : Countable (Matrix.GeneralLinearGroup (Fin 2) F) := Units.val_injective.countable
  have hUopen : IsOpen {g : AdelicGL2 (𝓞 F) F | φ g ≠ 0} := isOpen_ne_fun hcont continuous_const
  have hUne : ({g : AdelicGL2 (𝓞 F) F | φ g ≠ 0} : Set (AdelicGL2 (𝓞 F) F)).Nonempty := by
    obtain ⟨g, hg⟩ := hne
    exact ⟨g, hg⟩
  have hUγ : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      globalPoints (𝓞 F) F γ * g ∈ {g : AdelicGL2 (𝓞 F) F | φ g ≠ 0} ↔ g ∈ {g : AdelicGL2 (𝓞 F) F | φ g ≠ 0} := by
    intro γ g
    simp only [Set.mem_setOf_eq, hφ.left_invariant γ g]
  have hUz : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      centralScalar (𝓞 F) F z * g ∈ {g : AdelicGL2 (𝓞 F) F | φ g ≠ 0} ↔
        g ∈ {g : AdelicGL2 (𝓞 F) F | φ g ≠ 0} := by
    intro z g
    have hz : φ (centralScalar (𝓞 F) F z * g) = ((ξ ⟨z, hZ z⟩ : ℂˣ) : ℂ) * φ g :=
      hφ.central_transform ⟨z, hZ z⟩ g
    simp only [Set.mem_setOf_eq, hz, mul_ne_zero_iff]
    exact and_iff_right (Units.ne_zero _)
  rw [pos_iff_ne_zero]
  intro hWU
  have hpiece : ∀ k : ℕ, adelicGLHaar (Fin 2) (𝓞 F) F ({g : AdelicGL2 (𝓞 F) F | φ g ≠ 0} ∩
      {g : AdelicGL2 (𝓞 F) F | TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈
        Set.Icc (((k : ℝ) + 1)⁻¹) ((k : ℝ) + 1)}) = 0 := by
    intro k
    obtain ⟨N, hN⟩ := AutomorphicForm.exists_finset_central_slab_covering_of_coversModCentre F c u d₁ d₂ T
      hd hcov (((k : ℝ) + 1)⁻¹) ((k : ℝ) + 1) (by positivity)
    refine measure_mono_null (t := ⋃ γ : Matrix.GeneralLinearGroup (Fin 2) F, ⋃ n ∈ N,
      (fun h => globalPoints (𝓞 F) F γ * h) ⁻¹' ((fun h => centralScalar (𝓞 F) F n * h) ''
        ((⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) ∩ {g : AdelicGL2 (𝓞 F) F | φ g ≠ 0}))) ?_ ?_
    · rintro g ⟨hgU, hgslab⟩
      obtain ⟨γ, n, hn, x, hx, s, hs, hsx⟩ := hN g hgslab
      have hsx' : s * (centralScalar (𝓞 F) F n * x) = globalPoints (𝓞 F) F γ * g := hsx
      have hkey : globalPoints (𝓞 F) F γ * g = centralScalar (𝓞 F) F n * (s * x) := by
        rw [← hsx', ← mul_assoc, mul_centralScalar_comm, mul_assoc]
      refine Set.mem_iUnion.mpr ⟨γ, Set.mem_iUnion₂.mpr ⟨n, hn, ?_⟩⟩
      show globalPoints (𝓞 F) F γ * g ∈ (fun h => centralScalar (𝓞 F) F n * h) ''
        ((⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) ∩ {g : AdelicGL2 (𝓞 F) F | φ g ≠ 0})
      refine ⟨s * x, ⟨Set.mem_iUnion₂.mpr ⟨x, hx, ⟨s, hs, rfl⟩⟩, ?_⟩, hkey.symm⟩
      have h1 : globalPoints (𝓞 F) F γ * g ∈ {g : AdelicGL2 (𝓞 F) F | φ g ≠ 0} := (hUγ γ g).mpr hgU
      rw [hkey] at h1
      exact (hUz n (s * x)).mp h1
    · refine measure_iUnion_null_iff.mpr fun γ => (measure_biUnion_null_iff N.countable_toSet).mpr fun n _ => ?_
      rw [measure_preimage_mul, Set.image_mul_left, measure_preimage_mul]
      exact hWU
  have hcover : {g : AdelicGL2 (𝓞 F) F | φ g ≠ 0} ⊆ ⋃ k : ℕ, ({g : AdelicGL2 (𝓞 F) F | φ g ≠ 0} ∩
      {g : AdelicGL2 (𝓞 F) F | TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈
        Set.Icc (((k : ℝ) + 1)⁻¹) ((k : ℝ) + 1)}) := by
    intro g hg
    have hpos : 0 < TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) := TateGlobal.ideleNorm_pos _
    obtain ⟨k, hk⟩ := exists_nat_ge (max (TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g))⁻¹
      (TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g)))
    have hk1 : (TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g))⁻¹ ≤ (k : ℝ) + 1 :=
      (le_max_left _ _).trans (hk.trans (by linarith))
    have hk2 : TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ≤ (k : ℝ) + 1 :=
      (le_max_right _ _).trans (hk.trans (by linarith))
    exact Set.mem_iUnion.mpr ⟨k, hg, ⟨inv_le_of_inv_le₀ hpos hk1, hk2⟩⟩
  have hU0 : adelicGLHaar (Fin 2) (𝓞 F) F {g : AdelicGL2 (𝓞 F) F | φ g ≠ 0} = 0 := by
    refine le_antisymm ((measure_mono hcover).trans ((measure_iUnion_le _).trans ?_)) zero_le
    simp only [hpiece, tsum_zero, le_refl]
  exact (hUopen.measure_pos (adelicGLHaar (Fin 2) (𝓞 F) F) hUne).ne' hU0

omit [NumberField F] in
private theorem two_ne_zero_completion (w₀ : InfinitePlace F) : (2 : w₀.Completion) ≠ 0 := by
  intro h
  have h2 := norm_two_completion w₀
  rw [h, norm_zero] at h2
  norm_num at h2

private def smwScaleUnit (w₀ : InfinitePlace F) : (w₀.Completion)ˣ :=
  Units.mk0 (2 : w₀.Completion) (two_ne_zero_completion F w₀)

private def smwZ (w₀ : InfinitePlace F) (n : ℕ) : AdelicGL2 (𝓞 F) F :=
  centralScalar (𝓞 F) F (archCentralUnit F w₀ (smwScaleUnit F w₀ ^ n))

omit [NumberField F] in
private theorem norm_smwScaleUnit_pow (w₀ : InfinitePlace F) (n : ℕ) :
    ‖((smwScaleUnit F w₀ ^ n : (w₀.Completion)ˣ) : w₀.Completion)‖ = 2 ^ n := by
  rw [Units.val_pow_eq_pow_val, norm_pow]
  simp only [smwScaleUnit, Units.val_mk0, norm_two_completion]

private theorem archDetNorm_smwZ_mul (w₀ : InfinitePlace F) (n : ℕ) (g : AdelicGL2 (𝓞 F) F) :
    archDetNorm w₀ (smwZ F w₀ n * g) = 4 ^ n * archDetNorm w₀ g := by
  unfold smwZ
  rw [archDetNorm_centralScalar_mul, norm_smwScaleUnit_pow, ← mul_pow]
  norm_num

private theorem glFin_smwZ_mul (w₀ : InfinitePlace F) (n : ℕ) (g : AdelicGL2 (𝓞 F) F) :
    glFin (𝓞 F) F (smwZ F w₀ n * g) = glFin (𝓞 F) F g := by
  unfold smwZ
  rw [map_mul, glFin_centralScalar_archCentralUnit, one_mul]

private theorem coords_smwZ_mul (w₀ : InfinitePlace F) (n : ℕ) (g : AdelicGL2 (𝓞 F) F) :
    localHeight (archComponent F w₀ (glArch (𝓞 F) F (smwZ F w₀ n * g)))
        = localHeight (archComponent F w₀ (glArch (𝓞 F) F g)) ∧
      xWindowSq (archComponent F w₀ (glArch (𝓞 F) F (smwZ F w₀ n * g)))
        = xWindowSq (archComponent F w₀ (glArch (𝓞 F) F g)) := by
  unfold smwZ
  rw [map_mul, map_mul]
  have e := archComponent_centralScalar_archCentralUnit_apply (F := F) w₀ (smwScaleUnit F w₀ ^ n)
  have hne : ((smwScaleUnit F w₀ ^ n : (w₀.Completion)ˣ) : w₀.Completion) ≠ 0 := Units.ne_zero _
  exact ⟨localHeight_scalar_entries_mul hne (by rw [e]; rfl) (by rw [e]; rfl) (by rw [e]; rfl) (by rw [e]; rfl) _,
    xWindowSq_scalar_entries_mul hne (by rw [e]; rfl) (by rw [e]; rfl) (by rw [e]; rfl) (by rw [e]; rfl) _⟩

private theorem smwZ_mul_mem_iff (w₀ : InfinitePlace F) (hw₀ : ∀ w : InfinitePlace F, w = w₀) (n : ℕ)
    (c u a b : ℝ) (g : AdelicGL2 (𝓞 F) F) :
    smwZ F w₀ n * g ∈ centreCutSiegelSet F c u a b ↔ g ∈ centreCutSiegelSet F c u (a / 4 ^ n) (b / 4 ^ n) := by
  have h4 : (0 : ℝ) < 4 ^ n := by positivity
  rw [mem_centreCutSiegelSet_iff, mem_centreCutSiegelSet_iff, glFin_smwZ_mul]
  constructor
  · rintro ⟨h1, h2, h3, h5⟩
    refine ⟨h1, fun w => ?_, fun w => ?_, fun w => ?_⟩
    · rw [hw₀ w]
      have := h2 w₀
      rwa [(coords_smwZ_mul F w₀ n g).1] at this
    · rw [hw₀ w]
      have := h3 w₀
      rwa [(coords_smwZ_mul F w₀ n g).2] at this
    · rw [hw₀ w]
      have := h5 w₀
      rw [archDetNorm_smwZ_mul] at this
      exact ⟨(div_le_iff₀ h4).mpr (by linarith [this.1]), (le_div_iff₀ h4).mpr (by linarith [this.2])⟩
  · rintro ⟨h1, h2, h3, h5⟩
    refine ⟨h1, fun w => ?_, fun w => ?_, fun w => ?_⟩
    · rw [hw₀ w, (coords_smwZ_mul F w₀ n g).1]
      exact h2 w₀
    · rw [hw₀ w, (coords_smwZ_mul F w₀ n g).2]
      exact h3 w₀
    · rw [hw₀ w, archDetNorm_smwZ_mul]
      have := h5 w₀
      have ha := (div_le_iff₀ h4).mp this.1
      have hb := (le_div_iff₀ h4).mp this.2
      exact ⟨by linarith, by linarith⟩

private theorem mem_centreCutSiegelSet_of_det_window_le {c u a b a' b' : ℝ} (ha : a ≤ a') (hb : b' ≤ b)
    {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ centreCutSiegelSet F c u a' b') : g ∈ centreCutSiegelSet F c u a b := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_centreCutSiegelSet_iff.mp hg
  exact mem_centreCutSiegelSet_iff.mpr ⟨h1, h2, h3, fun w => ⟨ha.trans (h4 w).1, (h4 w).2.trans hb⟩⟩

private theorem archDetNorm_mul_right (w₀ : InfinitePlace F) (s x : AdelicGL2 (𝓞 F) F) :
    archDetNorm w₀ (s * x) = archDetNorm w₀ s * archDetNorm w₀ x := by
  unfold archDetNorm
  rw [map_mul, map_mul, Units.val_mul, Matrix.det_mul, norm_mul]

private def smwBase (w₀ : InfinitePlace F) (c u d₁ d₂ : ℝ) (x : AdelicGL2 (𝓞 F) F) : Set (AdelicGL2 (𝓞 F) F) :=
  (· * x) '' (centreCutSiegelSet F c u d₁ d₂ ∩ archDetNorm w₀ ⁻¹' Set.Ioi (d₂ / 4))

private def smwShell (w₀ : InfinitePlace F) (c u d₁ d₂ : ℝ) (x : AdelicGL2 (𝓞 F) F) (n : ℕ) :
    Set (AdelicGL2 (𝓞 F) F) :=
  (fun h => smwZ F w₀ n * h) ⁻¹' smwBase F w₀ c u d₁ d₂ x

private theorem measurableSet_smwBase (w₀ : InfinitePlace F) (c u d₁ d₂ : ℝ) (x : AdelicGL2 (𝓞 F) F) :
    letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
    MeasurableSet (smwBase F w₀ c u d₁ d₂ x) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  unfold smwBase
  rw [Set.image_mul_right]
  refine MeasurableSet.preimage ?_ (measurable_mul_const _)
  exact (measurableSet_centreCutSiegelSet c u d₁ d₂).inter
    (measurableSet_Ioi.preimage (continuous_archDetNorm (F := F) w₀).measurable)

private theorem measurableSet_smwShell (w₀ : InfinitePlace F) (c u d₁ d₂ : ℝ) (x : AdelicGL2 (𝓞 F) F) (n : ℕ) :
    letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
    MeasurableSet (smwShell F w₀ c u d₁ d₂ x n) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  have hb : MeasurableSet (smwBase F w₀ c u d₁ d₂ x) := measurableSet_smwBase F w₀ c u d₁ d₂ x
  exact hb.preimage (measurable_const_mul _)

private theorem det_bounds_of_mem_smwBase (w₀ : InfinitePlace F) {c u d₁ d₂ : ℝ} {x h : AdelicGL2 (𝓞 F) F}
    (hh : h ∈ smwBase F w₀ c u d₁ d₂ x) :
    d₂ / 4 * archDetNorm w₀ x < archDetNorm w₀ h ∧ archDetNorm w₀ h ≤ d₂ * archDetNorm w₀ x := by
  obtain ⟨s, ⟨hs, hlt⟩, rfl⟩ := hh
  have hlt' : d₂ / 4 < archDetNorm w₀ s := hlt
  have hx := archDetNorm_pos w₀ x
  have hsd := (mem_centreCutSiegelSet_iff.mp hs).2.2.2 w₀
  show d₂ / 4 * archDetNorm w₀ x < archDetNorm w₀ (s * x) ∧ archDetNorm w₀ (s * x) ≤ d₂ * archDetNorm w₀ x
  rw [archDetNorm_mul_right]
  exact ⟨mul_lt_mul_of_pos_right hlt' hx, mul_le_mul_of_nonneg_right hsd.2 hx.le⟩

private theorem smwShell_subset (w₀ : InfinitePlace F) (hw₀ : ∀ w : InfinitePlace F, w = w₀) (n : ℕ)
    {c u d₁ d₂ : ℝ} (hd₁ : d₁ ≤ 0) (hd₂ : 0 ≤ d₂) (x : AdelicGL2 (𝓞 F) F) :
    smwShell F w₀ c u d₁ d₂ x n ⊆ (· * x) '' centreCutSiegelSet F c u d₁ d₂ := by
  rintro h ⟨s, ⟨hs, -⟩, hsx⟩
  have hsx' : s * x = smwZ F w₀ n * h := hsx
  have h4 : (0 : ℝ) < 4 ^ n := by positivity
  have h41 : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
  refine ⟨(smwZ F w₀ n)⁻¹ * s, ?_, ?_⟩
  · have h1 : smwZ F w₀ n * ((smwZ F w₀ n)⁻¹ * s) ∈ centreCutSiegelSet F c u d₁ d₂ := by
      rwa [mul_inv_cancel_left]
    have h2 := (smwZ_mul_mem_iff F w₀ hw₀ n c u d₁ d₂ _).mp h1
    refine mem_centreCutSiegelSet_of_det_window_le F ?_ (div_le_self hd₂ h41) h2
    rw [le_div_iff₀ h4]
    nlinarith
  · show (smwZ F w₀ n)⁻¹ * s * x = h
    rw [mul_assoc, hsx', inv_mul_cancel_left]

private theorem smwShell_pairwise_disjoint (w₀ : InfinitePlace F) (c u d₁ d₂ : ℝ) (x : AdelicGL2 (𝓞 F) F) :
    Pairwise (Function.onFun Disjoint (smwShell F w₀ c u d₁ d₂ x)) := by
  intro m n hmn
  rw [Function.onFun, Set.disjoint_left]
  intro h hm hn
  have hD := archDetNorm_pos w₀ h
  obtain ⟨hm1, hm2⟩ := det_bounds_of_mem_smwBase F w₀ hm
  obtain ⟨hn1, hn2⟩ := det_bounds_of_mem_smwBase F w₀ hn
  rw [archDetNorm_smwZ_mul] at hm1 hm2 hn1 hn2
  have hE : d₂ * archDetNorm w₀ x = 4 * (d₂ / 4 * archDetNorm w₀ x) := by ring
  have key : ∀ a b : ℕ, (4 : ℝ) ^ a * archDetNorm w₀ h ≤ d₂ * archDetNorm w₀ x →
      d₂ / 4 * archDetNorm w₀ x < (4 : ℝ) ^ b * archDetNorm w₀ h → a ≤ b := by
    intro a b ha hb
    have h1 : (4 : ℝ) ^ a * archDetNorm w₀ h < 4 ^ (b + 1) * archDetNorm w₀ h := by
      rw [pow_succ]
      nlinarith
    have h2 : (4 : ℝ) ^ a < 4 ^ (b + 1) := lt_of_mul_lt_mul_right h1 hD.le
    have h3 := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 4)).mp h2
    omega
  exact hmn (le_antisymm (key m n hm2 hn1) (key n m hn2 hm1))

private theorem exists_shell_index {d₂ t : ℝ} (ht : 0 < t) (htd : t ≤ d₂) :
    ∃ n : ℕ, d₂ / 4 < 4 ^ n * t ∧ 4 ^ n * t ≤ d₂ := by
  have hex : ∃ m : ℕ, d₂ < 4 ^ (m + 1) * t := by
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (d₂ / t) (by norm_num : (1 : ℝ) < 4)
    refine ⟨m, ?_⟩
    have h1 : d₂ < 4 ^ m * t := (div_lt_iff₀ ht).mp hm
    have h2 : (4 : ℝ) ^ m * t ≤ 4 ^ (m + 1) * t :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Nat.le_succ m)) ht.le
    exact h1.trans_le h2
  classical
  refine ⟨Nat.find hex, ?_, ?_⟩
  · have h := Nat.find_spec hex
    rw [pow_succ] at h
    linarith
  · rcases hn : Nat.find hex with _ | k
    · simpa using htd
    · have hk : k < Nat.find hex := by omega
      exact not_lt.mp (Nat.find_min hex hk)

private theorem subset_iUnion_smwShell (w₀ : InfinitePlace F) (hw₀ : ∀ w : InfinitePlace F, w = w₀)
    (c u d₁ d₂ : ℝ) (hd₁ : d₁ ≤ 0) (hd₂ : 0 < d₂) (x : AdelicGL2 (𝓞 F) F) :
    (· * x) '' centreCutSiegelSet F c u d₁ d₂ ⊆ ⋃ n : ℕ, smwShell F w₀ c u d₁ d₂ x n := by
  rintro _ ⟨s, hs, rfl⟩
  have hsd := (mem_centreCutSiegelSet_iff.mp hs).2.2.2 w₀
  obtain ⟨n, hn1, hn2⟩ := exists_shell_index (archDetNorm_pos w₀ s) hsd.2
  have h4 : (0 : ℝ) < 4 ^ n := by positivity
  refine Set.mem_iUnion.mpr ⟨n, ?_⟩
  show smwZ F w₀ n * (s * x) ∈ smwBase F w₀ c u d₁ d₂ x
  refine ⟨smwZ F w₀ n * s, ⟨?_, ?_⟩, ?_⟩
  · rw [smwZ_mul_mem_iff F w₀ hw₀]
    obtain ⟨h1, h2, h3, -⟩ := mem_centreCutSiegelSet_iff.mp hs
    refine mem_centreCutSiegelSet_iff.mpr ⟨h1, h2, h3, fun w => ?_⟩
    rw [hw₀ w]
    have hpos := archDetNorm_pos w₀ s
    constructor
    · rw [div_le_iff₀ h4]
      nlinarith
    · rw [le_div_iff₀ h4]
      linarith
  · show d₂ / 4 < archDetNorm w₀ (smwZ F w₀ n * s)
    rw [archDetNorm_smwZ_mul]
    exact hn1
  · show smwZ F w₀ n * s * x = smwZ F w₀ n * (s * x)
    exact mul_assoc _ _ _

private def smwFactor (w₀ : InfinitePlace F) (Z : Subgroup (AdeleRing (𝓞 F) F)ˣ) (ξ : Z →* ℂˣ)
    (hZ : ∀ z, z ∈ Z) (n : ℕ) : ℝ≥0∞ :=
  ‖((ξ ⟨archCentralUnit F w₀ (smwScaleUnit F w₀ ^ n), hZ _⟩ : ℂˣ) : ℂ)‖ₑ ^ 2

private theorem smwFactor_ne_zero (w₀ : InfinitePlace F) (Z : Subgroup (AdeleRing (𝓞 F) F)ˣ) (ξ : Z →* ℂˣ)
    (hZ : ∀ z, z ∈ Z) (n : ℕ) : smwFactor F w₀ Z ξ hZ n ≠ 0 := by
  unfold smwFactor
  intro h0
  exact (ξ ⟨archCentralUnit F w₀ (smwScaleUnit F w₀ ^ n), hZ _⟩).ne_zero
    (enorm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h0))

private theorem smwFactor_ne_top (w₀ : InfinitePlace F) (Z : Subgroup (AdeleRing (𝓞 F) F)ˣ) (ξ : Z →* ℂˣ)
    (hZ : ∀ z, z ∈ Z) (n : ℕ) : smwFactor F w₀ Z ξ hZ n ≠ ⊤ := by
  unfold smwFactor
  exact ENNReal.pow_ne_top enorm_ne_top

private theorem lintegral_smwShell_eq (w₀ : InfinitePlace F) (c u d₁ d₂ : ℝ) (x : AdelicGL2 (𝓞 F) F) (n : ℕ)
    (Z : Subgroup (AdeleRing (𝓞 F) F)ˣ) (ξ : Z →* ℂˣ) (hZ : ∀ z, z ∈ Z)
    (ψ : AdelicGL2 (𝓞 F) F → ℂ) (hψ : IsLsXiFunction (𝓞 F) F Z ξ ψ) :
    letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
    ∫⁻ h in smwShell F w₀ c u d₁ d₂ x n, ‖ψ h‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
      = (smwFactor F w₀ Z ξ hZ n)⁻¹ *
          ∫⁻ h in smwBase F w₀ c u d₁ d₂ x, ‖ψ h‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have hκ0 := smwFactor_ne_zero F w₀ Z ξ hZ n
  have hκtop := smwFactor_ne_top F w₀ Z ξ hZ n
  have hlaw : ∀ h : AdelicGL2 (𝓞 F) F, ψ (smwZ F w₀ n * h)
      = ((ξ ⟨archCentralUnit F w₀ (smwScaleUnit F w₀ ^ n), hZ _⟩ : ℂˣ) : ℂ) * ψ h :=
    fun h => hψ.central_transform ⟨archCentralUnit F w₀ (smwScaleUnit F w₀ ^ n), hZ _⟩ h
  have hG : ∀ h : AdelicGL2 (𝓞 F) F, ‖ψ (smwZ F w₀ n * h)‖ₑ ^ 2 = smwFactor F w₀ Z ξ hZ n * ‖ψ h‖ₑ ^ 2 := by
    intro h
    unfold smwFactor
    rw [hlaw h, enorm_mul, mul_pow]
  have hbase : MeasurableSet (smwBase F w₀ c u d₁ d₂ x) := measurableSet_smwBase F w₀ c u d₁ d₂ x
  have hshell : MeasurableSet (smwShell F w₀ c u d₁ d₂ x n) := measurableSet_smwShell F w₀ c u d₁ d₂ x n
  have hind : ∀ h : AdelicGL2 (𝓞 F) F,
      (smwShell F w₀ c u d₁ d₂ x n).indicator (fun h => ‖ψ h‖ₑ ^ 2) h
        = (smwFactor F w₀ Z ξ hZ n)⁻¹ *
            (smwBase F w₀ c u d₁ d₂ x).indicator (fun h => ‖ψ h‖ₑ ^ 2) (smwZ F w₀ n * h) := by
    intro h
    by_cases hmem : h ∈ smwShell F w₀ c u d₁ d₂ x n
    · have hmem' : smwZ F w₀ n * h ∈ smwBase F w₀ c u d₁ d₂ x := hmem
      simp only [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem']
      rw [hG h, ← mul_assoc, ENNReal.inv_mul_cancel hκ0 hκtop, one_mul]
    · have hmem' : smwZ F w₀ n * h ∉ smwBase F w₀ c u d₁ d₂ x := hmem
      simp only [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem', mul_zero]
  calc ∫⁻ h in smwShell F w₀ c u d₁ d₂ x n, ‖ψ h‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
      = ∫⁻ h, (smwShell F w₀ c u d₁ d₂ x n).indicator (fun h => ‖ψ h‖ₑ ^ 2) h
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := (lintegral_indicator hshell _).symm
    _ = ∫⁻ h, (smwFactor F w₀ Z ξ hZ n)⁻¹ *
          (smwBase F w₀ c u d₁ d₂ x).indicator (fun h => ‖ψ h‖ₑ ^ 2) (smwZ F w₀ n * h)
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := lintegral_congr hind
    _ = (smwFactor F w₀ Z ξ hZ n)⁻¹ * ∫⁻ h,
          (smwBase F w₀ c u d₁ d₂ x).indicator (fun h => ‖ψ h‖ₑ ^ 2) (smwZ F w₀ n * h)
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hκ0)
    _ = (smwFactor F w₀ Z ξ hZ n)⁻¹ * ∫⁻ h, (smwBase F w₀ c u d₁ d₂ x).indicator (fun h => ‖ψ h‖ₑ ^ 2) h
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
        rw [lintegral_mul_left_eq_self ((smwBase F w₀ c u d₁ d₂ x).indicator (fun h => ‖ψ h‖ₑ ^ 2)) (smwZ F w₀ n)]
    _ = (smwFactor F w₀ Z ξ hZ n)⁻¹ *
          ∫⁻ h in smwBase F w₀ c u d₁ d₂ x, ‖ψ h‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
        rw [lintegral_indicator hbase]

private theorem smwBase_subset (w₀ : InfinitePlace F) (hw₀ : ∀ w : InfinitePlace F, w = w₀) (c u d₁ d₂ : ℝ)
    (x : AdelicGL2 (𝓞 F) F) :
    smwBase F w₀ c u d₁ d₂ x ⊆ (· * x) '' centreCutSiegelSet F c u (d₂ / 4) d₂ := by
  rintro _ ⟨s, ⟨hs, hlt⟩, rfl⟩
  refine ⟨s, ?_, rfl⟩
  have hlt' : d₂ / 4 < archDetNorm w₀ s := hlt
  obtain ⟨h1, h2, h3, h4⟩ := mem_centreCutSiegelSet_iff.mp hs
  refine mem_centreCutSiegelSet_iff.mpr ⟨h1, h2, h3, fun w => ?_⟩
  rw [hw₀ w]
  exact ⟨hlt'.le, (h4 w₀).2⟩

private theorem lintegral_smwBase_lt_top (w₀ : InfinitePlace F) (hw₀ : ∀ w : InfinitePlace F, w = w₀)
    (c u d₁ d₂ : ℝ) (hc : 0 < c) (hd₂ : 0 < d₂) (x : AdelicGL2 (𝓞 F) F)
    (ψ : AdelicGL2 (𝓞 F) F → ℂ) (hψc : Continuous ψ) (hψb : IsBoundedOnSiegelWindows F ψ) :
    letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
    ∫⁻ h in smwBase F w₀ c u d₁ d₂ x, ‖ψ h‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ⊤ := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  obtain ⟨C, hC⟩ := hψb c u (d₂ / 4) d₂ {x} hc (by positivity)
  simp only [Finset.set_biUnion_singleton] at hC
  have hfin : adelicGLHaar (Fin 2) (𝓞 F) F ((· * x) '' centreCutSiegelSet F c u (d₂ / 4) d₂) < ⊤ :=
    adelicGLHaar_mul_right_centreCutSiegelSet_lt_top F hc u (by positivity) d₂ x
  have hmem : MemLp ψ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict ((· * x) '' centreCutSiegelSet F c u (d₂ / 4) d₂)) :=
    memLp_two_restrict_of_bound F _ hfin ψ hψc C hC
  have hint : ∫⁻ h in (· * x) '' centreCutSiegelSet F c u (d₂ / 4) d₂, ‖ψ h‖ₑ ^ 2
      ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ⊤ := lintegral_enorm_sq_lt_top_of_memLp F _ ψ hmem
  exact lt_of_le_of_lt (lintegral_mono_set (smwBase_subset F w₀ hw₀ c u d₁ d₂ x)) hint

private theorem memLp_rightConv_of_nonpos [Countable F] (w₀ : InfinitePlace F)
    (hw₀ : ∀ w : InfinitePlace F, w = w₀) (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂) (hc : 0 < c) (hd₁ : d₁ ≤ 0)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : ((productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F))).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsSmoothCuspAutomorphicFnAt F
      ((productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F))) ξ φ)
    (hφc : Continuous φ) (hne : ∃ g, φ g ≠ 0) (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) :
    letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
    MemLp (rightConv F φ f) 2
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have hd₂ : 0 < d₂ := by
    by_contra hd₂'
    have hempty : centreCutSiegelSet F c u d₁ d₂ = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun g hg => ?_
      have h4 := (mem_centreCutSiegelSet_iff.mp hg).2.2.2 w₀
      exact not_le.mpr (archDetNorm_pos w₀ g) (h4.2.trans (not_lt.mp hd₂'))
    rw [hempty] at hcov
    simp only [Set.image_empty, Set.iUnion_empty] at hcov
    exact not_coversModCentre_empty hcov
  have hZ : ∀ z : (AdeleRing (𝓞 F) F)ˣ, z ∈ (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) := fun z => Subgroup.mem_top z
  have hauto : IsAutomorphicFnAt F
      ((productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F))) ξ φ := hφ.1.1
  have hls := (@lsXiMemberAt_iff (𝓞 F) F _ _ _ _ _ (glBorel (Fin 2) (𝓞 F) F) (adelicGLHaar (Fin 2) (𝓞 F) F) ⊤ ξ
    (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) φ).mp hauto
  have hlsxi : IsLsXiFunction (𝓞 F) F ⊤ ξ φ := hls.1
  have hφint : ∫⁻ h in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂, ‖φ h‖ₑ ^ 2
      ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ⊤ := lintegral_enorm_sq_lt_top_of_memLp F _ φ hls.2
  have hψc : Continuous (rightConv F φ f) :=
    (AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn F φ hφc f hf).1
  have hψls : IsLsXiFunction (𝓞 F) F ⊤ ξ (rightConv F φ f) :=
    isLsXiFunction_rightConv_of_isLsXiFunction F ⊤ ξ hlsxi f
  have hψb : IsBoundedOnSiegelWindows F (rightConv F φ f) :=
    AutomorphicForm.isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_coversModCentre F c u d₁ d₂ T
      hd hcov ξ φ hφ.1 hφc f hf
  have hWU := measure_window_inter_support_pos F c u d₁ d₂ T hd hcov ⊤ ξ hZ φ hlsxi hφc hne

  have hx : ∃ x ∈ T, 0 < adelicGLHaar (Fin 2) (𝓞 F) F
      ((· * x) '' centreCutSiegelSet F c u d₁ d₂ ∩ {g : AdelicGL2 (𝓞 F) F | φ g ≠ 0}) := by
    by_contra hcon
    have hall : ∀ x ∈ T, adelicGLHaar (Fin 2) (𝓞 F) F
        ((· * x) '' centreCutSiegelSet F c u d₁ d₂ ∩ {g : AdelicGL2 (𝓞 F) F | φ g ≠ 0}) = 0 := fun x hxT =>
      le_antisymm (not_lt.mp fun hlt => hcon ⟨x, hxT, hlt⟩) zero_le
    refine hWU.ne' (measure_mono_null ?_ ((measure_biUnion_null_iff T.countable_toSet).mpr hall))
    rintro g ⟨hgW, hgU⟩
    obtain ⟨x, hxT, hgx⟩ := Set.mem_iUnion₂.mp hgW
    exact Set.mem_iUnion₂.mpr ⟨x, hxT, hgx, hgU⟩
  obtain ⟨x₀, hx₀T, hx₀⟩ := hx

  have hn : ∃ n : ℕ, 0 < adelicGLHaar (Fin 2) (𝓞 F) F
      (smwShell F w₀ c u d₁ d₂ x₀ n ∩ {g : AdelicGL2 (𝓞 F) F | φ g ≠ 0}) := by
    by_contra hcon
    have hall : ∀ n : ℕ, adelicGLHaar (Fin 2) (𝓞 F) F
        (smwShell F w₀ c u d₁ d₂ x₀ n ∩ {g : AdelicGL2 (𝓞 F) F | φ g ≠ 0}) = 0 := fun n =>
      le_antisymm (not_lt.mp fun hlt => hcon ⟨n, hlt⟩) zero_le
    refine hx₀.ne' (measure_mono_null ?_ (measure_iUnion_null_iff.mpr hall))
    rintro g ⟨hgS, hgU⟩
    obtain ⟨n, hgn⟩ := Set.mem_iUnion.mp (subset_iUnion_smwShell F w₀ hw₀ c u d₁ d₂ hd₁ hd₂ x₀ hgS)
    exact Set.mem_iUnion.mpr ⟨n, hgn, hgU⟩
  obtain ⟨n₀, hn₀⟩ := hn
  have hmeasφ : Measurable fun h : AdelicGL2 (𝓞 F) F => ‖φ h‖ₑ ^ 2 := hφc.measurable.enorm.pow_const 2
  have hIn : 0 < ∫⁻ h in smwShell F w₀ c u d₁ d₂ x₀ n₀, ‖φ h‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
    rw [setLIntegral_pos_iff hmeasφ]
    refine hn₀.trans_le (measure_mono ?_)
    rintro g ⟨hgn, hgU⟩
    have hgU' : φ g ≠ 0 := hgU
    refine ⟨?_, hgn⟩
    show ‖φ g‖ₑ ^ 2 ≠ 0
    exact fun h0 => hgU' (enorm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h0))
  have hI0 : 0 < ∫⁻ h in smwBase F w₀ c u d₁ d₂ x₀, ‖φ h‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
    rw [lintegral_smwShell_eq F w₀ c u d₁ d₂ x₀ n₀ ⊤ ξ hZ φ hlsxi] at hIn
    exact (ENNReal.mul_pos_iff.mp hIn).2

  have hsum : (∑' n : ℕ, (smwFactor F w₀ ⊤ ξ hZ n)⁻¹) *
        ∫⁻ h in smwBase F w₀ c u d₁ d₂ x₀, ‖φ h‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
      ≤ ∫⁻ h in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂, ‖φ h‖ₑ ^ 2
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
    rw [← ENNReal.tsum_mul_right]
    calc ∑' n : ℕ, (smwFactor F w₀ ⊤ ξ hZ n)⁻¹ *
            ∫⁻ h in smwBase F w₀ c u d₁ d₂ x₀, ‖φ h‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
        = ∑' n : ℕ, ∫⁻ h in smwShell F w₀ c u d₁ d₂ x₀ n, ‖φ h‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) :=
          tsum_congr fun n => (lintegral_smwShell_eq F w₀ c u d₁ d₂ x₀ n ⊤ ξ hZ φ hlsxi).symm
      _ = ∫⁻ h in ⋃ n : ℕ, smwShell F w₀ c u d₁ d₂ x₀ n, ‖φ h‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) :=
          (lintegral_iUnion (fun n => measurableSet_smwShell F w₀ c u d₁ d₂ x₀ n)
            (smwShell_pairwise_disjoint F w₀ c u d₁ d₂ x₀) _).symm
      _ ≤ ∫⁻ h in (· * x₀) '' centreCutSiegelSet F c u d₁ d₂, ‖φ h‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) :=
          lintegral_mono_set (Set.iUnion_subset fun n => smwShell_subset F w₀ hw₀ n hd₁ hd₂.le x₀)
      _ ≤ ∫⁻ h in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂, ‖φ h‖ₑ ^ 2
            ∂(adelicGLHaar (Fin 2) (𝓞 F) F) :=
          lintegral_mono_set (Set.subset_iUnion₂ (s := fun x (_ : x ∈ T) => (· * x) '' centreCutSiegelSet F c u d₁ d₂)
            x₀ hx₀T)
  have hM : (∑' n : ℕ, (smwFactor F w₀ ⊤ ξ hZ n)⁻¹) < ⊤ := by
    by_contra htop
    rw [not_lt, top_le_iff] at htop
    rw [htop, ENNReal.top_mul hI0.ne'] at hsum
    exact hφint.ne (top_le_iff.mp hsum)

  have hψx : ∀ y ∈ T, ∫⁻ h in (· * y) '' centreCutSiegelSet F c u d₁ d₂, ‖rightConv F φ f h‖ₑ ^ 2
      ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ⊤ := by
    intro y _
    have hJ : ∫⁻ h in smwBase F w₀ c u d₁ d₂ y, ‖rightConv F φ f h‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ⊤ :=
      lintegral_smwBase_lt_top F w₀ hw₀ c u d₁ d₂ hc hd₂ y (rightConv F φ f) hψc hψb
    calc ∫⁻ h in (· * y) '' centreCutSiegelSet F c u d₁ d₂, ‖rightConv F φ f h‖ₑ ^ 2
            ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
        ≤ ∫⁻ h in ⋃ n : ℕ, smwShell F w₀ c u d₁ d₂ y n, ‖rightConv F φ f h‖ₑ ^ 2
            ∂(adelicGLHaar (Fin 2) (𝓞 F) F) :=
          lintegral_mono_set (subset_iUnion_smwShell F w₀ hw₀ c u d₁ d₂ hd₁ hd₂ y)
      _ ≤ ∑' n : ℕ, ∫⁻ h in smwShell F w₀ c u d₁ d₂ y n, ‖rightConv F φ f h‖ₑ ^ 2
            ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := lintegral_iUnion_le _ _
      _ = ∑' n : ℕ, (smwFactor F w₀ ⊤ ξ hZ n)⁻¹ *
            ∫⁻ h in smwBase F w₀ c u d₁ d₂ y, ‖rightConv F φ f h‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) :=
          tsum_congr fun n => lintegral_smwShell_eq F w₀ c u d₁ d₂ y n ⊤ ξ hZ (rightConv F φ f) hψls
      _ = (∑' n : ℕ, (smwFactor F w₀ ⊤ ξ hZ n)⁻¹) *
            ∫⁻ h in smwBase F w₀ c u d₁ d₂ y, ‖rightConv F φ f h‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) :=
          ENNReal.tsum_mul_right
      _ < ⊤ := ENNReal.mul_lt_top hM hJ
  have hsub : (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
      ⊆ ⋃ x : T, (· * (x : AdelicGL2 (𝓞 F) F)) '' centreCutSiegelSet F c u d₁ d₂ := by
    intro g hg
    obtain ⟨x, hxT, hgx⟩ := Set.mem_iUnion₂.mp hg
    exact Set.mem_iUnion.mpr ⟨⟨x, hxT⟩, hgx⟩
  have hWint : ∫⁻ h in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂, ‖rightConv F φ f h‖ₑ ^ 2
      ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ⊤ := by
    calc ∫⁻ h in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂, ‖rightConv F φ f h‖ₑ ^ 2
            ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
        ≤ ∫⁻ h in ⋃ x : T, (· * (x : AdelicGL2 (𝓞 F) F)) '' centreCutSiegelSet F c u d₁ d₂,
            ‖rightConv F φ f h‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := lintegral_mono_set hsub
      _ ≤ ∑' x : T, ∫⁻ h in (· * (x : AdelicGL2 (𝓞 F) F)) '' centreCutSiegelSet F c u d₁ d₂,
            ‖rightConv F φ f h‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := lintegral_iUnion_le _ _
      _ = ∑ x : T, ∫⁻ h in (· * (x : AdelicGL2 (𝓞 F) F)) '' centreCutSiegelSet F c u d₁ d₂,
            ‖rightConv F φ f h‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := tsum_fintype _
      _ < ⊤ := ENNReal.sum_lt_top.mpr fun x _ => hψx x x.2
  exact memLp_of_lintegral_enorm_sq_lt_top F _ _ hψc hWint

private theorem memLp_rightConv_of_lt (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂) (hc : 0 < c) (hd₁ : 0 < d₁)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : ((productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F))).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsSmoothCuspAutomorphicFnAt F
      ((productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F))) ξ φ)
    (hφc : Continuous φ) (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) :
    letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
    MemLp (rightConv F φ f) 2
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) := by
  have hcont : Continuous (rightConv F φ f) :=
    (AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn F φ hφc f hf).1
  obtain ⟨C, hC⟩ :=
    AutomorphicForm.exists_forall_norm_rightConv_le_mul_eLpNorm_of_isSmoothCuspAutomorphicFnAt_of_coversModCentre
      F c u d₁ d₂ T hc hd₁ hd hcov ξ f hf
  have hbound := hC φ hφ hφc
  have hfin : adelicGLHaar (Fin 2) (𝓞 F) F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) < ⊤ := by
    letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
    exact measure_biUnion_lt_top T.finite_toSet
      (fun x _ => adelicGLHaar_mul_right_centreCutSiegelSet_lt_top F hc u hd₁ d₂ x)
  exact memLp_two_restrict_of_bound F _ hfin (rightConv F φ f) hcont _ hbound

private theorem memLp_rightConv_window [Countable F] (w₀ : InfinitePlace F) (hw₀ : ∀ w : InfinitePlace F, w = w₀)
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Φ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F))
      Φ.toRawCentral)
    (hR : Continuous R.toFun) (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) :
    letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
    MemLp (rightConv F R.toFun f) 2
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) := by
  by_cases hc : c ≤ 0
  · exact ((AutomorphicForm.not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre F c u d₁ d₂ T
      hc hd hcov Φ) ⟨R, hR⟩).elim
  · have hc' : 0 < c := not_le.mp hc
    by_cases hd₁ : 0 < d₁
    · exact memLp_rightConv_of_lt F c u d₁ d₂ T hd hc' hd₁ hcov R.centralChar R.toFun R.smoothCusp hR f hf
    · exact memLp_rightConv_of_nonpos F w₀ hw₀ c u d₁ d₂ T hd hc' (not_lt.mp hd₁) hcov R.centralChar R.toFun
        R.smoothCusp hR R.exists_ne_zero f hf

private theorem memLp_rightConv_window_rat (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ))
      Φ.toRawCentral)
    (hR : Continuous R.toFun) (f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hf : IsFactorizableTestFn ℚ f) :
    letI : MeasurableSpace (AdelicGL2 (𝓞 ℚ) ℚ) := glBorel (Fin 2) (𝓞 ℚ) ℚ
    MemLp (rightConv ℚ R.toFun f) 2
      ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)) :=
  memLp_rightConv_window ℚ default (fun w => Subsingleton.elim w default) c u d₁ d₂ T hd hcov Φ R hR f hf

end SmwShell

end ModShells

section ModConvHalfR

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

namespace IsotypicConvolution

private theorem isIsotypicCuspFormAt_rightConv_of_memLp (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (Φ : HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ))
      Φ.toRawCentral)
    (hR : Continuous R.toFun) (f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hf : IsFactorizableTestFn ℚ f)
    (hfs : ∀ x, f x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 ℚ) ℚ,
      glFin (𝓞 ℚ) ℚ a = 1 ∧ k ∈ levelOne (𝓞 ℚ) ℚ Φ.level ⊓ finiteAdelicGL2Subgroup ℚ ∧ x = a * k)
    (hmem : letI : MeasurableSpace (AdelicGL2 (𝓞 ℚ) ℚ) := glBorel (Fin 2) (𝓞 ℚ) ℚ
      MemLp (rightConv ℚ R.toFun f) 2
        ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))) :
    IsIsotypicCuspFormAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ))
      R.centralChar Φ.level R.exceptionalSet Φ (rightConv ℚ R.toFun f) := by
  obtain ⟨hcusp, hkf, hlev, hhecke⟩ :=
    AutomorphicForm.isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset
      ℚ c u d₁ d₂ T Φ.toRawCentral R hR f hf hfs
  have hcont : Continuous (rightConv ℚ R.toFun f) :=
    (AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn ℚ R.toFun hR f hf).1
  have hauto : IsAutomorphicFnAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ))
      R.centralChar R.toFun := R.smoothCusp.1.1
  have hlsxi : IsLsXiFunction (𝓞 ℚ) ℚ ⊤ R.centralChar R.toFun :=
    ((@lsXiMemberAt_iff (𝓞 ℚ) ℚ _ _ _ _ _ (glBorel (Fin 2) (𝓞 ℚ) ℚ) (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) ⊤ R.centralChar
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) R.toFun).mp hauto).1
  have hauto' : IsAutomorphicFnAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ))
      R.centralChar (rightConv ℚ R.toFun f) :=
    (@lsXiMemberAt_iff (𝓞 ℚ) ℚ _ _ _ _ _ (glBorel (Fin 2) (𝓞 ℚ) ℚ) (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) ⊤ R.centralChar
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) (rightConv ℚ R.toFun f)).mpr
      ⟨SmwShell.isLsXiFunction_rightConv_of_isLsXiFunction ℚ ⊤ R.centralChar hlsxi f, hmem⟩
  exact ⟨⟨⟨hauto', hcusp⟩, hkf⟩, hcont, hlev, hhecke,
    fun v hv g => SmwShell.rightConv_mul_left_of_forall_mul ℚ (fun x => R.central_eigen v hv x) g⟩

end IsotypicConvolution

end ModConvHalfR

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open LanglandsTunnell LanglandsTunnell.Converse NumberField.TateGlobal

theorem solution
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ))
      Φ.toRawCentral)
    (hR : Continuous R.toFun) (f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hf : IsFactorizableTestFn ℚ f)
    (hfs : ∀ x : AdelicGL2 (𝓞 ℚ) ℚ, f x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 ℚ) ℚ,
      glFin (𝓞 ℚ) ℚ a = 1 ∧ k ∈ levelOne (𝓞 ℚ) ℚ Φ.level ⊓ finiteAdelicGL2Subgroup ℚ ∧ x = a * k) :
    IsIsotypicCuspFormAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ))
      R.centralChar Φ.level R.exceptionalSet Φ (rightConv ℚ R.toFun f) :=
  IsotypicConvolution.isIsotypicCuspFormAt_rightConv_of_memLp c u d₁ d₂ T Φ R hR f hf hfs
    (SmwShell.memLp_rightConv_window_rat c u d₁ d₂ T hd hcov Φ R hR f hf)

end

end S_AutomorphicForm_isIsotypicCuspFormAt_rightConv_of_isFactorizableTestFn_of_support_subset_of_coversModCentre
end P2MW
export P2MW.S_AutomorphicForm_isIsotypicCuspFormAt_rightConv_of_isFactorizableTestFn_of_support_subset_of_coversModCentre (solution)
