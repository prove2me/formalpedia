-- Prove2me | solution 1 for AutomorphicForm.isArithBoundedGenuineCuspRealizable_of_isArithGenuineCuspRealizable_of_coversModCentre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/de04ba1e-1cd9-5426-a63c-dbbade213778

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Theorems.Thm_AutomorphicForm_isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_coversModCentre
import Theorems.Thm_AutomorphicForm_whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff_mixedSpace
import Theorems.Thm_AutomorphicForm_isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset
import Theorems.Thm_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_exists_isFactorizableTestFn_rightConv_ne_zero_of_levelOne_invariant
import Theorems.Thm_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isArithBoundedGenuineCuspRealizable_of_isArithGenuineCuspRealizable_of_coversModCentre
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open MeasureTheory AutomorphicForm AutomorphicForm.SmoothCusp

namespace BoundednessUpgrade

variable {K : Type} [Field K] [NumberField K]

private theorem globalPoints_unipotentGL2 (β : K) :
    globalPoints (𝓞 K) K (unipotentGL2 β) =
      unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [globalPoints, unipotentGL2, Matrix.GeneralLinearGroup.map, RingHom.mapMatrix_apply]

private theorem rightConv_mul_left_of_invariant (φ f : AdelicGL2 (𝓞 K) K → ℂ)
    (h : AdelicGL2 (𝓞 K) K) (hφ : ∀ x, φ (h * x) = φ x) (g : AdelicGL2 (𝓞 K) K) :
    rightConv K φ f (h * g) = rightConv K φ f g := by
  rw [← rightConv_comp_mul_left]
  exact congrArg (fun ψ => rightConv K ψ f g) (funext hφ)

private theorem rightConv_mul_left_of_eq_smul (φ f : AdelicGL2 (𝓞 K) K → ℂ)
    (h : AdelicGL2 (𝓞 K) K) (a : ℂ) (hφ : ∀ x, φ (h * x) = a * φ x) (g : AdelicGL2 (𝓞 K) K) :
    rightConv K φ f (h * g) = a * rightConv K φ f g := by
  rw [← rightConv_comp_mul_left, (funext hφ : (fun x => φ (h * x)) = fun x => a * φ x)]
  simp only [rightConv, mul_assoc]
  exact integral_const_mul a _

private theorem memLp_two_restrict_of_norm_le {α : Type*} {m : MeasurableSpace α}
    {μ : Measure α} {D : Set α} (hD : μ D < ⊤) {φ : α → ℂ} (hmeas : AEStronglyMeasurable φ (μ.restrict D))
    (hDm : MeasurableSet D) {C : ℝ} (hC : ∀ g ∈ D, ‖φ g‖ ≤ C) :
    MemLp φ 2 (μ.restrict D) := by
  haveI : IsFiniteMeasure (μ.restrict D) := isFiniteMeasure_restrict.mpr hD.ne
  exact MemLp.of_bound hmeas C ((ae_restrict_iff' hDm).mpr (Filter.Eventually.of_forall hC))

end BoundednessUpgrade

open BoundednessUpgrade in

theorem solution
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c)
    (hd₁ : 0 < d₁)
    (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (Φ : HeckeEigensystem K ℂ)
    (hΦ : IsArithGenuineCuspRealizable K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Φ) :
    IsArithBoundedGenuineCuspRealizable K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (StandardAddChar.stdAddChar K) Φ := by
  classical

  obtain ⟨R, hRc⟩ := hΦ
  change Continuous R.toFun at hRc
  letI : MeasurableSpace (AdelicGL2 (𝓞 K) K) := glBorel (Fin 2) (𝓞 K) K
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  have hLs := ((lsXiMemberAt_iff (𝓞 K) K _ _ R.centralChar _ R.toFun).mp R.smoothCusp.1.1).1

  obtain ⟨f, hf, -, hfs, g₀, hg₀⟩ :=
    AutomorphicForm.exists_isFactorizableTestFn_rightConv_ne_zero_of_levelOne_invariant
      K Φ.toRawCentral.level Φ.toRawCentral.level_ne_bot R.toFun hRc R.exists_ne_zero
      R.level_invariant

  obtain ⟨hcusp, hsm, hlev, hhecke⟩ :=
    AutomorphicForm.isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset
      K c u d₁ d₂ T Φ.toRawCentral R hRc f hf hfs

  obtain ⟨hcont', harch⟩ :=
    AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn K R.toFun hRc f hf

  have hLs' : IsLsXiFunction (𝓞 K) K _ R.centralChar (rightConv K R.toFun f) :=
    ⟨fun γ g => rightConv_mul_left_of_invariant R.toFun f _ (hLs.left_invariant γ) g,
     fun z g => rightConv_mul_left_of_eq_smul R.toFun f _ _ (hLs.central_transform z) g⟩

  have hG : IsBoundedOnSiegelWindows K (rightConv K R.toFun f) :=
    AutomorphicForm.isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_coversModCentre
      K c u d₁ d₂ T hd hcov R.centralChar R.toFun R.smoothCusp.1 hRc f hf

  have hDm : MeasurableSet (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) := by
    refine T.measurableSet_biUnion fun x _ => ?_
    have h := (MeasurableEquiv.mulRight x).measurableSet_image.mpr
      (measurableSet_centreCutSiegelSet (F := K) c u d₁ d₂)
    simpa only [MeasurableEquiv.coe_mulRight] using h
  have hDfin : adelicGLHaar (Fin 2) (𝓞 K) K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) < ⊤ := by
    refine lt_of_le_of_lt (measure_biUnion_finset_le T _) ?_
    exact ENNReal.sum_lt_top.mpr fun x _ =>
      adelicGLHaar_mul_right_centreCutSiegelSet_lt_top K hc u hd₁ d₂ x
  obtain ⟨C, hC⟩ := hG c u d₁ d₂ T hc hd₁
  have hMem : MemLp (rightConv K R.toFun f) 2
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)) :=
    memLp_two_restrict_of_norm_le hDfin hcont'.aestronglyMeasurable hDm hC

  have hleftU : ∀ (β : K) (g : AdelicGL2 (𝓞 K) K),
      rightConv K R.toFun f (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * g)
        = rightConv K R.toFun f g := fun β g => by
    rw [← globalPoints_unipotentGL2]; exact hLs'.left_invariant _ g
  have hC4 :=
    AutomorphicForm.whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff_mixedSpace
      K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
      (StandardAddChar.stdAddChar K) (StandardAddChar.isGlobalAddChar_stdAddChar K)
      (rightConv K R.toFun f) hleftU hsm harch

  exact ⟨{ toFun := rightConv K R.toFun f
           exists_ne_zero := ⟨g₀, hg₀⟩
           centralChar := R.centralChar
           smoothCusp := ⟨⟨(lsXiMemberAt_iff (𝓞 K) K _ _ R.centralChar _ _).mpr ⟨hLs', hMem⟩,
             hcusp⟩, hsm⟩
           level_invariant := hlev
           exceptionalSet := R.exceptionalSet
           hecke_eigen := hhecke
           central_eigen := fun v hv g =>
             rightConv_mul_left_of_eq_smul R.toFun f _ _ (R.central_eigen v hv) g },
    hcont', hG, hC4.1, hC4.2⟩

end S_AutomorphicForm_isArithBoundedGenuineCuspRealizable_of_isArithGenuineCuspRealizable_of_coversModCentre
end P2MW
export P2MW.S_AutomorphicForm_isArithBoundedGenuineCuspRealizable_of_isArithGenuineCuspRealizable_of_coversModCentre (solution)
