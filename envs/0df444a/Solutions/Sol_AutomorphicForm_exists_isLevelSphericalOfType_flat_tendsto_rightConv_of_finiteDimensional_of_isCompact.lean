-- Prove2me | solution 1 for AutomorphicForm.exists_isLevelSphericalOfType_flat_tendsto_rightConv_of_finiteDimensional_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/946b5a17-4665-53bd-a611-2d7a37f1bd0f

import Mathlib
import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ArchSpherical
import Theorems.Thm_AutomorphicForm_isCompact_rowIsometrySubgroup_detOne
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_of_isHaarMeasure_generalLinearGroup_infiniteAdeleRing
import Theorems.Thm_AutomorphicForm_finiteDimensional_span_translates_of_mem_archCutSubmodule
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_exists_isArchTestFactor_nonneg_and_tsupport_subset_and_conj_invariant_and_flat
import Theorems.Thm_AutomorphicForm_exists_pos_forall_rightConv_integral_prod_mul_indicator_eq_mul_integral_of_forall_integral_mul_apply_mul_eq
import Theorems.Thm_AutomorphicForm_exists_continuous_conj_invariant_integral_mul_apply_mul_eq_of_finiteDimensional_of_le_archCutSubmodule
import Theorems.Thm_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule
import Theorems.Thm_AutomorphicForm_integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isLevelSphericalOfType_flat_tendsto_rightConv_of_finiteDimensional_of_isCompact
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv"
p2m_attr_erase "simp" "RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_isLevelSphericalOfType_flat_tendsto_rightConv_of_finiteDimensional_of_isCompact.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering"
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rowIsometryInclAt₀ commute_archGLIncl_of_ne ArchTypeFamily archCutSubmodule archRowIsometryInclAt₀ archFactorCutSubmodule archFactorDualCutSubmodule IsArchFactorBiFinite AdelicGL2 finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff rightConv rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff archMatrixPiEquiv archMatrixUpdate archMatrixPiEquiv_archMatrixUpdate adelicMatrixProdEquiv adelicArchGLIncl glArch_adelicArchGLIncl glFin_adelicArchGLIncl archEntries IsArchTestFactor IsFinTestFactor IsFactorizableTestFn IsArchSphericalOfType IsLevelSphericalOfType finiteDimensional_span_translates_of_mem_archCutSubmodule continuous_and_hasCompactSupport_of_isFactorizableTestFn exists_isArchTestFactor_nonneg_and_tsupport_subset_and_conj_invariant_and_flat exists_pos_forall_rightConv_integral_prod_mul_indicator_eq_mul_integral_of_forall_integral_mul_apply_mul_eq exists_continuous_conj_invariant_integral_mul_apply_mul_eq_of_finiteDimensional_of_le_archCutSubmodule isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat"
namespace C2ABridge
p2m_open "AutomorphicForm"

variable (F : Type) [Field F] [NumberField F]

def adelicFinGLIncl : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) →* AdelicGL2 (𝓞 F) F :=
  (Units.mapEquiv (adelicMatrixProdEquiv F).symm.toMulEquiv).toMonoidHom.comp <|
    (MulEquiv.prodUnits.symm : _ ≃* (_ × _)ˣ).toMonoidHom.comp <|
      MonoidHom.prod (1 : _ →* GL (Fin 2) (InfiniteAdeleRing F)) (MonoidHom.id _)

theorem glArch_adelicFinGLIncl (k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    glArch (𝓞 F) F (adelicFinGLIncl F k) = 1 := by
  ext i j
  rfl

theorem glFin_adelicFinGLIncl (k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    glFin (𝓞 F) F (adelicFinGLIncl F k) = k := by
  ext i j
  rfl

theorem adelicFinGLIncl_mem_finiteAdelicGL2Subgroup (k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    adelicFinGLIncl F k ∈ finiteAdelicGL2Subgroup F :=
  (mem_finiteAdelicGL2Subgroup_iff F _).2 (glArch_adelicFinGLIncl F k)

theorem continuous_adelicFinGLIncl : Continuous (adelicFinGLIncl F) := by
  have hval : Continuous fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) =>
      ((adelicFinGLIncl F g : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
    refine continuous_matrix fun i j => ?_
    show Continuous fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) =>
      (((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
        (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) :
          InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
    exact continuous_const.prodMk (Units.continuous_val.matrix_elem i j)
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  simp only [← map_inv]
  exact hval.comp continuous_inv

theorem adelicFinGLIncl_glFin_of_glArch_eq_one (g : AdelicGL2 (𝓞 F) F) (hg : glArch (𝓞 F) F g = 1) :
    adelicFinGLIncl F (glFin (𝓞 F) F g) = g := by
  ext i j
  refine Prod.ext ?_ rfl
  exact (congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing F) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j)
    hg).symm

theorem adelicArchGLIncl_glArch_of_glFin_eq_one (g : AdelicGL2 (𝓞 F) F) (hg : glFin (𝓞 F) F g = 1) :
    adelicArchGLIncl F (glArch (𝓞 F) F g) = g := by
  ext i j
  refine Prod.ext rfl ?_
  exact (congrArg (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) =>
    (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) hg).symm

theorem image_glFin_eq_preimage (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hUf : U ≤ finiteAdelicGL2Subgroup F) :
    (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))
      = adelicFinGLIncl F ⁻¹' (U : Set (AdelicGL2 (𝓞 F) F)) := by
  ext m
  constructor
  · rintro ⟨g, hg, rfl⟩
    show adelicFinGLIncl F (glFin (𝓞 F) F g) ∈ (U : Set (AdelicGL2 (𝓞 F) F))
    rw [adelicFinGLIncl_glFin_of_glArch_eq_one F g ((mem_finiteAdelicGL2Subgroup_iff F g).1 (hUf hg))]
    exact hg
  · intro hm
    exact ⟨adelicFinGLIncl F m, hm, glFin_adelicFinGLIncl F m⟩

theorem isOpen_image_glFin (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F))) :
    IsOpen ((glFin (𝓞 F) F) '' (↑(O ⊓ finiteAdelicGL2Subgroup F) : Set (AdelicGL2 (𝓞 F) F))) := by
  rw [image_glFin_eq_preimage F _ inf_le_right]
  have h : adelicFinGLIncl F ⁻¹' (↑(O ⊓ finiteAdelicGL2Subgroup F) : Set (AdelicGL2 (𝓞 F) F))
      = adelicFinGLIncl F ⁻¹' (O : Set (AdelicGL2 (𝓞 F) F)) := by
    ext m
    simp only [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, adelicFinGLIncl_mem_finiteAdelicGL2Subgroup F m⟩⟩
  rw [h]
  exact hO.preimage (continuous_adelicFinGLIncl F)

theorem isCompact_image_glFin (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F))) :
    IsCompact ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) :=
  hU.image (continuous_glFin (𝓞 F) F)

open NumberField.TateGlobal in
theorem ideleNorm_det_eq_one_of_isCompact_of_mem
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (u : AdelicGL2 (𝓞 F) F) (hu : u ∈ U) :
    ideleNorm F (Matrix.GeneralLinearGroup.det u) = 1 := by

  have hcont : Continuous fun g : AdelicGL2 (𝓞 F) F => ideleNorm F (Matrix.GeneralLinearGroup.det g) :=
    NumberField.TateGlobal.continuous_ideleNorm_det F
  have hmul : ∀ a b : AdelicGL2 (𝓞 F) F, ideleNorm F (Matrix.GeneralLinearGroup.det (a * b)) =
      ideleNorm F (Matrix.GeneralLinearGroup.det a) * ideleNorm F (Matrix.GeneralLinearGroup.det b) := by
    intro a b; rw [map_mul, ideleNorm_mul]
  have hpow : ∀ (n : ℕ), ideleNorm F (Matrix.GeneralLinearGroup.det (u ^ n)) =
      ideleNorm F (Matrix.GeneralLinearGroup.det u) ^ n := by
    intro n
    induction n with
    | zero => simp [NumberField.TateGlobal.ideleNorm]
    | succ n ih => rw [pow_succ u n, hmul, ih, ← pow_succ]

  obtain ⟨M, hM⟩ := (hU.image hcont).isBounded.bddAbove
  have hbd : ∀ g ∈ U, ideleNorm F (Matrix.GeneralLinearGroup.det g) ≤ M := fun g hg => hM ⟨g, hg, rfl⟩
  set x := ideleNorm F (Matrix.GeneralLinearGroup.det u) with hx
  have hxpos : 0 < x := ideleNorm_pos _

  have hup : ∀ n : ℕ, x ^ n ≤ M := fun n => by rw [← hpow]; exact hbd _ (U.pow_mem hu n)
  have hinv : ideleNorm F (Matrix.GeneralLinearGroup.det u⁻¹) = x⁻¹ := by
    have h1 : ideleNorm F (Matrix.GeneralLinearGroup.det (u * u⁻¹)) = 1 := by
      rw [mul_inv_cancel]; simp [NumberField.TateGlobal.ideleNorm]
    rw [hmul] at h1
    exact (eq_inv_of_mul_eq_one_right h1)
  have hpow' : ∀ n : ℕ, ideleNorm F (Matrix.GeneralLinearGroup.det (u⁻¹ ^ n)) = x⁻¹ ^ n := by
    intro n
    induction n with
    | zero => simp [NumberField.TateGlobal.ideleNorm]
    | succ n ih => rw [pow_succ u⁻¹ n, hmul, ih, hinv, ← pow_succ]
  have hdown : ∀ n : ℕ, x⁻¹ ^ n ≤ M := fun n => by
    rw [← hpow']; exact hbd _ (U.pow_mem (U.inv_mem hu) n)
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  ·
    have h1 : 1 < x⁻¹ := (one_lt_inv₀ hxpos).mpr hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M h1
    exact absurd (hdown n) (not_le.mpr hn)
  · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M hgt
    exact absurd (hup n) (not_le.mpr hn)

end AutomorphicForm.C2ABridge

end

noncomputable section

open MeasureTheory Filter Topology

namespace ApproxIdentity

variable {H : Type*} [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H]
variable (ν : Measure H) [IsFiniteMeasureOnCompacts ν] (x₀ : H)

theorem tendsto_integral_mul
    {ψ : ℕ → H → ℝ} (hcont : ∀ n, Continuous (ψ n))
    (hcs : ∀ n, HasCompactSupport (ψ n)) (hnn : ∀ n g, 0 ≤ ψ n g)
    (hint : ∀ n, (∫ g, ψ n g ∂ν) = 1)
    (hsupp : ∀ U ∈ 𝓝 x₀, ∀ᶠ n in atTop, tsupport (ψ n) ⊆ U)
    {φ : H → ℂ} (hφ : Continuous φ) :
    Tendsto (fun n => ∫ g, φ g * (ψ n g : ℂ) ∂ν) atTop (𝓝 (φ x₀)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hV : φ ⁻¹' Metric.ball (φ x₀) (ε / 2) ∈ 𝓝 x₀ :=
    hφ.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ (by positivity))
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (hsupp _ hV)
  refine ⟨n₀, fun n hn => ?_⟩
  have hsub := hn₀ n hn
  have hψc : Continuous fun g => (ψ n g : ℂ) := Complex.continuous_ofReal.comp (hcont n)
  have hψcs : HasCompactSupport fun g => (ψ n g : ℂ) :=
    (hcs n).comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hi₁ : Integrable (fun g => φ g * (ψ n g : ℂ)) ν :=
    (hφ.mul hψc).integrable_of_hasCompactSupport hψcs.mul_left
  have hi₂ : Integrable (fun g => φ x₀ * (ψ n g : ℂ)) ν :=
    (continuous_const.mul hψc).integrable_of_hasCompactSupport hψcs.mul_left
  have h1 : (∫ g, φ x₀ * (ψ n g : ℂ) ∂ν) = φ x₀ := by
    calc (∫ g, φ x₀ * (ψ n g : ℂ) ∂ν) = φ x₀ * ∫ g, (ψ n g : ℂ) ∂ν := integral_const_mul _ _
      _ = φ x₀ * ((∫ g, ψ n g ∂ν : ℝ) : ℂ) := by rw [integral_complex_ofReal]
      _ = φ x₀ := by rw [hint n, Complex.ofReal_one, mul_one]
  have hdiff : (∫ g, φ g * (ψ n g : ℂ) ∂ν) - φ x₀ = ∫ g, (φ g - φ x₀) * (ψ n g : ℂ) ∂ν := by
    calc (∫ g, φ g * (ψ n g : ℂ) ∂ν) - φ x₀
        = (∫ g, φ g * (ψ n g : ℂ) ∂ν) - ∫ g, φ x₀ * (ψ n g : ℂ) ∂ν := by rw [h1]
      _ = ∫ g, (φ g * (ψ n g : ℂ) - φ x₀ * (ψ n g : ℂ)) ∂ν := (integral_sub hi₁ hi₂).symm
      _ = ∫ g, (φ g - φ x₀) * (ψ n g : ℂ) ∂ν := by simp only [sub_mul]
  have hbound : ∀ g, ‖(φ g - φ x₀) * (ψ n g : ℂ)‖ ≤ ε / 2 * ψ n g := by
    intro g
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hnn n g)]
    by_cases hg : g ∈ tsupport (ψ n)
    · have hlt : ‖φ g - φ x₀‖ < ε / 2 := by
        have h := Metric.mem_ball.mp (hsub hg)
        rwa [dist_eq_norm] at h
      exact mul_le_mul_of_nonneg_right hlt.le (hnn n g)
    · simp [image_eq_zero_of_notMem_tsupport hg]
  have hi₃ : Integrable (fun g => ‖(φ g - φ x₀) * (ψ n g : ℂ)‖) ν :=
    (((hφ.sub continuous_const).mul hψc).integrable_of_hasCompactSupport hψcs.mul_left).norm
  have hi₄ : Integrable (fun g => ε / 2 * ψ n g) ν :=
    (continuous_const.mul (hcont n)).integrable_of_hasCompactSupport (hcs n).mul_left
  rw [dist_eq_norm, hdiff]
  calc ‖∫ g, (φ g - φ x₀) * (ψ n g : ℂ) ∂ν‖
      ≤ ∫ g, ‖(φ g - φ x₀) * (ψ n g : ℂ)‖ ∂ν := norm_integral_le_integral_norm _
    _ ≤ ∫ g, ε / 2 * ψ n g ∂ν := integral_mono hi₃ hi₄ hbound
    _ = ε / 2 * ∫ g, ψ n g ∂ν := integral_const_mul _ _
    _ = ε / 2 := by rw [hint n, mul_one]
    _ < ε := half_lt_self hε

theorem integral_pos [ν.IsOpenPosMeasure]
    {ψ : H → ℝ} (hcont : Continuous ψ) (hcs : HasCompactSupport ψ) (hnn : ∀ g, 0 ≤ ψ g) (h0 : 0 < ψ x₀) :
    0 < ∫ g, ψ g ∂ν :=
  hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs (fun g => hnn g) h0.ne'

theorem tendsto_inv_integral_mul_integral_mul [ν.IsOpenPosMeasure]
    {ψ : ℕ → H → ℝ} (hcont : ∀ n, Continuous (ψ n))
    (hcs : ∀ n, HasCompactSupport (ψ n)) (hnn : ∀ n g, 0 ≤ ψ n g) (h0 : ∀ n, 0 < ψ n x₀)
    (hsupp : ∀ U ∈ 𝓝 x₀, ∀ᶠ n in atTop, tsupport (ψ n) ⊆ U)
    {φ : H → ℂ} (hφ : Continuous φ) :
    Tendsto (fun n => (∫ g, (ψ n g : ℂ) ∂ν)⁻¹ * ∫ g, φ g * (ψ n g : ℂ) ∂ν) atTop (𝓝 (φ x₀)) := by
  have hI : ∀ n, 0 < ∫ g, ψ n g ∂ν := fun n => integral_pos ν x₀ (hcont n) (hcs n) (hnn n) (h0 n)
  let ψ' : ℕ → H → ℝ := fun n g => ψ n g / ∫ g, ψ n g ∂ν
  have hcont' : ∀ n, Continuous (ψ' n) := fun n => (hcont n).div_const _
  have hcs' : ∀ n, HasCompactSupport (ψ' n) := fun n => by
    show HasCompactSupport fun g => ψ n g / ∫ g, ψ n g ∂ν
    simp_rw [div_eq_mul_inv]
    exact (hcs n).mul_right
  have hnn' : ∀ n g, 0 ≤ ψ' n g := fun n g => div_nonneg (hnn n g) (hI n).le
  have hint' : ∀ n, (∫ g, ψ' n g ∂ν) = 1 := fun n => by
    show (∫ g, ψ n g / ∫ g, ψ n g ∂ν ∂ν) = 1
    rw [integral_div, div_self (hI n).ne']
  have hsupp' : ∀ U ∈ 𝓝 x₀, ∀ᶠ n in atTop, tsupport (ψ' n) ⊆ U := fun U hU =>
    (hsupp U hU).mono fun n hn => by
      refine Set.Subset.trans ?_ hn
      show tsupport (fun g => ψ n g / ∫ g, ψ n g ∂ν) ⊆ tsupport (ψ n)
      simp_rw [div_eq_mul_inv]
      exact tsupport_mul_subset_left
  have hlim := tendsto_integral_mul ν x₀ hcont' hcs' hnn' hint' hsupp' hφ
  refine hlim.congr fun n => ?_
  have hIc : ((∫ g, (ψ n g : ℂ) ∂ν)) = ((∫ g, ψ n g ∂ν : ℝ) : ℂ) := integral_complex_ofReal
  have hne : ((∫ g, ψ n g ∂ν : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hI n).ne'
  rw [hIc, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  show φ g * ((ψ n g / ∫ g, ψ n g ∂ν : ℝ) : ℂ) = ((∫ g, ψ n g ∂ν : ℝ) : ℂ)⁻¹ * (φ g * (ψ n g : ℂ))
  push_cast
  field_simp

end ApproxIdentity

end

section Gamma4Block

open NumberField
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_isLevelSphericalOfType_flat_tendsto_rightConv_of_finiteDimensional_of_isCompact.AutomorphicForm"
open MeasureTheory Topology

noncomputable section

namespace R5bC

variable (F : Type) [Field F] [NumberField F]

private theorem secondCountableTopology_infiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing F) := by
  haveI : ∀ w : InfinitePlace F, ProperSpace w.Completion :=
    fun w => NumberField.AdelicBox.properSpace_completion (K := F) w
  exact inferInstanceAs (SecondCountableTopology ((w : InfinitePlace F) → w.Completion))

private theorem secondCountableTopology_archMatrix :
    SecondCountableTopology (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) := by
  haveI := secondCountableTopology_infiniteAdeleRing F
  exact inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → InfiniteAdeleRing F))

omit [NumberField F] in
private theorem t2Space_archMatrix' : T2Space (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
  inferInstanceAs (T2Space (Fin 2 → Fin 2 → InfiniteAdeleRing F))

private theorem secondCountableTopology_archGL : SecondCountableTopology (GL (Fin 2) (InfiniteAdeleRing F)) := by
  haveI := secondCountableTopology_archMatrix F

  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

private theorem locallyCompactSpace_archMatrix :
    LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
  inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → InfiniteAdeleRing F))

private theorem locallyCompactSpace_archGL : LocallyCompactSpace (GL (Fin 2) (InfiniteAdeleRing F)) := by
  haveI := t2Space_archMatrix' F
  haveI := locallyCompactSpace_archMatrix F
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

omit [NumberField F] in
private theorem secondCountableTopology_placeGL (w : InfinitePlace F) :
    SecondCountableTopology (GL (Fin 2) w.Completion) := by
  haveI : ProperSpace w.Completion := NumberField.AdelicBox.properSpace_completion (K := F) w
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) w.Completion) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → w.Completion))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) w.Completion)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

omit [NumberField F] in
private theorem secondCountableTopology_rowIsometrySubgroup₀ (w : InfinitePlace F) :
    SecondCountableTopology (rowIsometrySubgroup₀ w.Completion) := by
  haveI := secondCountableTopology_placeGL F w

  exact Topology.IsEmbedding.subtypeVal.secondCountableTopology

private theorem secondCountableTopology_piRowIsometrySubgroup₀ :
    SecondCountableTopology (Π w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) := by
  haveI : ∀ w : InfinitePlace F, SecondCountableTopology (rowIsometrySubgroup₀ w.Completion) :=
    secondCountableTopology_rowIsometrySubgroup₀ F
  infer_instance

omit [NumberField F] in
private theorem isTopologicalGroup_archGL : IsTopologicalGroup (GL (Fin 2) (InfiniteAdeleRing F)) := inferInstance

end R5bC

end

end Gamma4Block

section AlphaBlock

open NumberField NumberField.AdelicLevel
open AutomorphicForm.WindowedSiegel
open IsDedekindDomain
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_isLevelSphericalOfType_flat_tendsto_rightConv_of_finiteDimensional_of_isCompact.AutomorphicForm"

noncomputable section

namespace R5bK

attribute [local instance] R5bC.t2Space_archMatrix' R5bC.locallyCompactSpace_archMatrix
  R5bC.locallyCompactSpace_archGL R5bC.isTopologicalGroup_archGL
  R5bC.secondCountableTopology_archGL R5bC.secondCountableTopology_piRowIsometrySubgroup₀

section Compact

variable (K : Type*) [NormedField K]

private def rowIsoSet : Set (Matrix (Fin 2) (Fin 2) K) :=
  {m | m.det = 1} ∩ ({m | ‖m.det‖ = 1} ∩ ⋂ x : K, ⋂ y : K,
    {m | ‖x * m 0 0 + y * m 1 0‖ ^ 2 + ‖x * m 0 1 + y * m 1 1‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2})

private theorem mem_rowIsoSet_iff (k : GL (Fin 2) K) :
    (k : Matrix (Fin 2) (Fin 2) K) ∈ rowIsoSet K ↔ k ∈ rowIsometrySubgroup₀ K := by
  simp only [rowIsoSet, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq,
    mem_rowIsometrySubgroup₀_iff, IsRowIsometry]

private theorem continuous_entry (i j : Fin 2) :
    Continuous fun m : Matrix (Fin 2) (Fin 2) K => m i j :=
  continuous_id.matrix_elem i j

private theorem isClosed_rowIsoSet : IsClosed (rowIsoSet K) := by
  have hdet : Continuous fun m : Matrix (Fin 2) (Fin 2) K => m.det := continuous_id.matrix_det
  refine (isClosed_eq hdet continuous_const).inter
    ((isClosed_eq hdet.norm continuous_const).inter ?_)
  refine isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq ?_ continuous_const
  have h0 : Continuous fun m : Matrix (Fin 2) (Fin 2) K => x * m 0 0 + y * m 1 0 :=
    (continuous_const.mul (continuous_entry K 0 0)).add
      (continuous_const.mul (continuous_entry K 1 0))
  have h1 : Continuous fun m : Matrix (Fin 2) (Fin 2) K => x * m 0 1 + y * m 1 1 :=
    (continuous_const.mul (continuous_entry K 0 1)).add
      (continuous_const.mul (continuous_entry K 1 1))
  exact (h0.norm.pow 2).add (h1.norm.pow 2)

private theorem norm_entry_le_one {m : Matrix (Fin 2) (Fin 2) K} (hm : m ∈ rowIsoSet K) (i j : Fin 2) :
    ‖m i j‖ ≤ 1 := by
  have hrow : ∀ x y : K,
      ‖x * m 0 0 + y * m 1 0‖ ^ 2 + ‖x * m 0 1 + y * m 1 1‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
    have h := hm.2.2
    simp only [Set.mem_iInter, Set.mem_setOf_eq] at h
    exact h
  have hr0 : ‖m 0 0‖ ^ 2 + ‖m 0 1‖ ^ 2 = 1 := by
    have h := hrow 1 0
    simpa using h
  have hr1 : ‖m 1 0‖ ^ 2 + ‖m 1 1‖ ^ 2 = 1 := by
    have h := hrow 0 1
    simpa using h
  have key : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a ^ 2 + b ^ 2 = 1 → a ≤ 1 := by
    intro a b ha hb h
    nlinarith [sq_nonneg b, sq_nonneg (a - 1)]
  fin_cases i <;> fin_cases j
  · exact key _ _ (norm_nonneg _) (norm_nonneg _) hr0
  · exact key _ _ (norm_nonneg _) (norm_nonneg _) (by rw [add_comm]; exact hr0)
  · exact key _ _ (norm_nonneg _) (norm_nonneg _) hr1
  · exact key _ _ (norm_nonneg _) (norm_nonneg _) (by rw [add_comm]; exact hr1)

private theorem isCompact_rowIsoSet [ProperSpace K] : IsCompact (rowIsoSet K) := by
  have hbox : IsCompact ((Set.pi Set.univ fun _ : Fin 2 =>
      Set.pi Set.univ fun _ : Fin 2 => Metric.closedBall (0 : K) 1) :
        Set (Matrix (Fin 2) (Fin 2) K)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine hbox.of_isClosed_subset (isClosed_rowIsoSet K) fun m hm => ?_
  exact Set.mem_univ_pi.mpr fun i => Set.mem_univ_pi.mpr fun j =>
    mem_closedBall_zero_iff.mpr (norm_entry_le_one K hm i j)

private def toUnit (m : rowIsoSet K) : GL (Fin 2) K where
  val := m.1
  inv := m.1.adjugate
  val_inv := by
    have hd : m.1.det = 1 := m.2.1
    rw [Matrix.mul_adjugate, hd, one_smul]
  inv_val := by
    have hd : m.1.det = 1 := m.2.1
    rw [Matrix.adjugate_mul, hd, one_smul]

private theorem continuous_toUnit : Continuous (toUnit K) :=
  Units.continuous_iff.mpr ⟨continuous_subtype_val, continuous_subtype_val.matrix_adjugate⟩

private theorem range_toUnit :
    Set.range (toUnit K) = (rowIsometrySubgroup₀ K : Set (GL (Fin 2) K)) := by
  ext k
  constructor
  · rintro ⟨m, rfl⟩
    exact (mem_rowIsoSet_iff K (toUnit K m)).mp m.2
  · intro hk
    exact ⟨⟨(k : Matrix (Fin 2) (Fin 2) K), (mem_rowIsoSet_iff K k).mpr hk⟩, Units.ext rfl⟩

private theorem isCompact_rowIsometrySubgroup₀ [ProperSpace K] :
    IsCompact (rowIsometrySubgroup₀ K : Set (GL (Fin 2) K)) := by
  rw [← range_toUnit]
  haveI : CompactSpace (rowIsoSet K) := isCompact_iff_compactSpace.mp (isCompact_rowIsoSet K)
  exact isCompact_range (continuous_toUnit K)

end Compact

section Setting

variable (F : Type) [Field F] [NumberField F]

private abbrev Kw (w : InfinitePlace F) : Type := rowIsometrySubgroup₀ w.Completion

private abbrev Kprod : Type := Π w : InfinitePlace F, Kw F w

private scoped instance compactSpace_Kw (w : InfinitePlace F) : CompactSpace (Kw F w) :=
  haveI : ProperSpace w.Completion := NumberField.AdelicBox.properSpace_completion (K := F) w
  isCompact_iff_compactSpace.mp (isCompact_rowIsometrySubgroup₀ w.Completion)

omit [NumberField F] in
private theorem commute_archRowIsometryInclAt₀ {v w : InfinitePlace F} (hvw : v ≠ w) (a : Kw F v) (b : Kw F w) :
    Commute (archRowIsometryInclAt₀ F v a) (archRowIsometryInclAt₀ F w b) := by
  unfold archRowIsometryInclAt₀
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
  exact commute_archGLIncl_of_ne F hvw _ _

private def inclArch : Kprod F →* GL (Fin 2) (InfiniteAdeleRing F) :=
  MonoidHom.noncommPiCoprod (archRowIsometryInclAt₀ F)
    (fun _ _ hvw => commute_archRowIsometryInclAt₀ F hvw)

private def inclAdelic : Kprod F →* AdelicGL2 (𝓞 F) F :=
  (adelicArchGLIncl F).comp (inclArch F)

variable {F}

private theorem inclAdelic_apply (κ : Kprod F) : inclAdelic F κ = adelicArchGLIncl F (inclArch F κ) :=
  rfl

private theorem inclArch_mulSingle [DecidableEq (InfinitePlace F)] (w : InfinitePlace F) (k : Kw F w) :
    inclArch F (Pi.mulSingle w k) = archRowIsometryInclAt₀ F w k :=
  MonoidHom.noncommPiCoprod_mulSingle _ w k

private theorem inclAdelic_mulSingle [DecidableEq (InfinitePlace F)] (w : InfinitePlace F) (k : Kw F w) :
    inclAdelic F (Pi.mulSingle w k) = rowIsometryInclAt₀ F w k :=
  congrArg (adelicArchGLIncl F) (inclArch_mulSingle w k)

private theorem inclArch_entry (κ : Kprod F) (i j : Fin 2) (w : InfinitePlace F) :
    ((inclArch F κ : GL (Fin 2) (InfiniteAdeleRing F)) :
        Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j w
      = ((κ w : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j := by
  classical
  let f : Kprod F →* (Π v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion) :=
    ((archMatrixPiEquiv F : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) →*
        Π v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion).comp
      (Units.coeHom (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)))).comp (inclArch F)
  let g : Kprod F →* (Π v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion) :=
    MonoidHom.pi fun v : InfinitePlace F =>
      ((Units.coeHom (Matrix (Fin 2) (Fin 2) v.Completion)).comp
        (rowIsometrySubgroup₀ v.Completion).subtype).comp
          (Pi.evalMonoidHom (fun u : InfinitePlace F => Kw F u) v)
  have hfg : f = g := by
    refine MonoidHom.pi_ext fun v k => ?_
    funext u
    show archMatrixPiEquiv F
        ((inclArch F (Pi.mulSingle v k) : GL (Fin 2) (InfiniteAdeleRing F)) :
          Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) u
      = ((Pi.mulSingle v k u : Kw F u) : GL (Fin 2) u.Completion)
    rw [inclArch_mulSingle]
    show archMatrixPiEquiv F (archMatrixUpdate F v ((k : GL (Fin 2) v.Completion) :
        Matrix (Fin 2) (Fin 2) v.Completion)) u = _
    rw [archMatrixPiEquiv_archMatrixUpdate]
    by_cases huv : u = v
    · subst huv
      simp
    · simp [Function.update_of_ne huv, Pi.mulSingle_eq_of_ne huv]
  have h : f κ = g κ := by rw [hfg]
  have hw := congrFun h w
  exact congrFun (congrFun hw i) j

private theorem archComponent_inclArch (κ : Kprod F) (w : InfinitePlace F) :
    archComponent F w (inclArch F κ) = (κ w : GL (Fin 2) w.Completion) := by
  ext i j
  rw [AdelicLevel.archComponent_apply, inclArch_entry]

private theorem continuous_inclArch : Continuous (inclArch F) := by
  have hval : Continuous fun κ : Kprod F =>
      ((inclArch F κ : GL (Fin 2) (InfiniteAdeleRing F)) :
        Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) := by
    refine continuous_matrix fun i j => ?_
    refine continuous_pi fun w => ?_
    simp only [inclArch_entry]
    exact (Units.continuous_val.comp (continuous_subtype_val.comp (continuous_apply w))).matrix_elem
      i j
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  simp only [← map_inv]
  exact hval.comp continuous_inv

private theorem continuous_adelicArchGLIncl : Continuous (adelicArchGLIncl F) := by
  have hval : Continuous fun g : GL (Fin 2) (InfiniteAdeleRing F) =>
      ((adelicArchGLIncl F g : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
    refine continuous_matrix fun i j => ?_
    show Continuous fun g : GL (Fin 2) (InfiniteAdeleRing F) =>
      (((g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
        (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) :
          InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
    exact (Units.continuous_val.matrix_elem i j).prodMk continuous_const
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  simp only [← map_inv]
  exact hval.comp continuous_inv

private theorem continuous_inclAdelic : Continuous (inclAdelic F) :=
  continuous_adelicArchGLIncl.comp continuous_inclArch

end Setting

section HaarKprod

open MeasureTheory TopologicalSpace

variable (F : Type) [Field F]

private abbrev KprodMeasurableSpace : MeasurableSpace (Kprod F) := borel (Kprod F)

attribute [local instance] KprodMeasurableSpace

private theorem KprodBorelSpace : BorelSpace (Kprod F) := ⟨rfl⟩

attribute [local instance] KprodBorelSpace

private def KprodTop : PositiveCompacts (Kprod F) where
  carrier := Set.univ
  isCompact' := isCompact_univ
  interior_nonempty' := by
    rw [interior_univ]
    exact ⟨1, Set.mem_univ 1⟩

private def muK : Measure (Kprod F) := Measure.haarMeasure (KprodTop F)

private theorem muK_univ : muK F Set.univ = 1 :=
  Measure.haarMeasure_self (K₀ := KprodTop F)

private scoped instance isProbabilityMeasure_muK : IsProbabilityMeasure (muK F) := ⟨muK_univ F⟩

private scoped instance isMulLeftInvariant_muK : (muK F).IsMulLeftInvariant := by
  unfold muK
  infer_instance

private scoped instance isHaarMeasure_muK : (muK F).IsHaarMeasure := by
  unfold muK
  infer_instance

private theorem isMulRightInvariant_muK : (muK F).IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have hg : Measurable fun κ : Kprod F => κ * g := (continuous_mul_const g).measurable
  haveI : IsFiniteMeasureOnCompacts (Measure.map (· * g) (muK F)) := ⟨fun _ _ => measure_lt_top _ _⟩
  have hfac : (Measure.map (· * g) (muK F)).haarScalarFactor (muK F) = 1 := by
    have h := Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure (Measure.map (· * g) (muK F))
      (muK F) (s := Set.univ) isClosed_closure.isCompact
    rw [Measure.map_apply hg MeasurableSet.univ, Set.preimage_univ, muK_univ, ENNReal.smul_def, smul_eq_mul,
      mul_one] at h
    exact ENNReal.coe_eq_one.mp h.symm
  ext s _
  rw [Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure (Measure.map (· * g) (muK F)) (muK F)
    isClosed_closure.isCompact, hfac, one_smul]

private theorem integral_mul_right_muK (h : Kprod F → ℂ) (k : Kprod F) :
    ∫ κ, h (κ * k) ∂muK F = ∫ κ, h κ ∂muK F :=
  haveI := isMulRightInvariant_muK F
  integral_mul_right_eq_self h k

private theorem integral_mul_left_muK (h : Kprod F → ℂ) (k : Kprod F) :
    ∫ κ, h (k * κ) ∂muK F = ∫ κ, h κ ∂muK F :=
  integral_mul_left_eq_self h k

end HaarKprod

end R5bK
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isLevelSphericalOfType_flat_tendsto_rightConv_of_finiteDimensional_of_isCompact.R5bK"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isLevelSphericalOfType_flat_tendsto_rightConv_of_finiteDimensional_of_isCompact.R5bK"

end AlphaBlock
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isLevelSphericalOfType_flat_tendsto_rightConv_of_finiteDimensional_of_isCompact.R5bK"

section C2ABlock

open MeasureTheory TopologicalSpace

namespace R5bK

variable (F : Type) [Field F] [NumberField F]

attribute [local instance] KprodMeasurableSpace KprodBorelSpace

private theorem isInvInvariant_muK : (muK F).IsInvInvariant := by
  haveI := isMulRightInvariant_muK F
  refine ⟨?_⟩
  haveI : IsFiniteMeasureOnCompacts (muK F).inv := ⟨fun _ _ => measure_lt_top _ _⟩
  have hfac : (muK F).inv.haarScalarFactor (muK F) = 1 := by
    have h := Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure (muK F).inv (muK F)
      (s := Set.univ) isClosed_closure.isCompact
    rw [Measure.inv_apply, Set.inv_univ, muK_univ, ENNReal.smul_def, smul_eq_mul, mul_one] at h
    exact ENNReal.coe_eq_one.mp h.symm
  ext s _
  rw [Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure (muK F).inv (muK F)
    isClosed_closure.isCompact, hfac, one_smul]

end R5bK
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isLevelSphericalOfType_flat_tendsto_rightConv_of_finiteDimensional_of_isCompact.R5bK"

end C2ABlock
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isLevelSphericalOfType_flat_tendsto_rightConv_of_finiteDimensional_of_isCompact.R5bK"

open NumberField.TateGlobal in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    (tys : AutomorphicForm.ArchTypeFamily F) (σ : ℝ)
    (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hY : FiniteDimensional ℂ ↥Y)
    (hYc : ∀ y ∈ Y, Continuous y)
    (hYU : ∀ y ∈ Y, ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, y (g * k) = y g)
    (hYt : Y ≤ archCutSubmodule F tys) :
    ∃ f : ℕ → (AdelicGL2 (𝓞 F) F → ℂ),
      (∀ n, IsFactorizableTestFn F (f n) ∧
        IsLevelSphericalOfType F tys U (f n) ∧
        flat F σ (f n) = f n) ∧
      ∀ y ∈ Y, ∀ g : AdelicGL2 (𝓞 F) F,
        Filter.Tendsto (fun n => rightConv F y (f n) g) Filter.atTop (nhds (y g)) := by
  classical
  haveI : FiniteDimensional ℂ ↥Y := hY

  have hUf : U ≤ finiteAdelicGL2Subgroup F := hUO ▸ inf_le_right
  have hS : (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) = ↑(U.map (glFin (𝓞 F) F)) :=
    (Subgroup.coe_map _ _).symm
  have hSinv : ∀ z : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F z ∈ (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) →
      glFin (𝓞 F) F z⁻¹ ∈ (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) := by
    intro z hz
    rw [hS, SetLike.mem_coe] at hz ⊢
    rw [map_inv]
    exact inv_mem hz
  have hUo : IsOpen ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) := by
    rw [hUO]
    exact AutomorphicForm.C2ABridge.isOpen_image_glFin F O hO
  have hUc : IsCompact ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) :=
    AutomorphicForm.C2ABridge.isCompact_image_glFin F U hU

  haveI : T2Space (Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → FiniteAdeleRing (𝓞 F) F))
  haveI : T2Space (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) := Units.isEmbedding_embedProduct.t2Space
  have hcl : IsClosed ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) := hUc.isClosed
  have hfin : IsFinTestFactor F
      (Set.indicator ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ))) := by
    refine ⟨?_, HasCompactSupport.intro hUc fun x hx => Set.indicator_of_notMem hx _⟩
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    by_cases hx : x ∈ (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))
    · exact ⟨_, hUo, hx, fun x' hx' => by rw [Set.indicator_of_mem hx', Set.indicator_of_mem hx]⟩
    · exact ⟨_, hcl.isOpen_compl, hx, fun x' hx' => by
        rw [Set.indicator_of_notMem (show x' ∉ _ from hx'), Set.indicator_of_notMem hx]⟩
  have h1S : ∀ x : GL (Fin 2) (InfiniteAdeleRing F),
      glFin (𝓞 F) F (adelicArchGLIncl F x) ∈ (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) :=
    fun x => ⟨1, U.one_mem, by rw [map_one, glFin_adelicArchGLIncl]⟩
  have hTcont : ∀ ψ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ, IsArchTestFactor F ψ → Continuous ψ := by
    intro ψ hψ
    have hF := (AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F
      (fun g => ψ (glArch (𝓞 F) F g) *
        Set.indicator ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ)) (glFin (𝓞 F) F g))
      ⟨ψ, _, hψ, hfin, fun g => rfl⟩).1
    have heq : ψ = fun x => ψ (glArch (𝓞 F) F (adelicArchGLIncl F x)) *
        Set.indicator ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ))
          (glFin (𝓞 F) F (adelicArchGLIncl F x)) := by
      funext x
      simp only [glArch_adelicArchGLIncl, Set.indicator_of_mem (h1S x), mul_one]
    rw [heq]
    exact hF.comp R5bK.continuous_adelicArchGLIncl

  letI : MeasurableSpace (R5bK.Kprod F) := R5bK.KprodMeasurableSpace F
  haveI : BorelSpace (R5bK.Kprod F) := R5bK.KprodBorelSpace F
  let μ : Measure (R5bK.Kprod F) := R5bK.muK F
  haveI : IsProbabilityMeasure μ := R5bK.isProbabilityMeasure_muK F
  haveI : μ.IsMulLeftInvariant := R5bK.isMulLeftInvariant_muK F
  haveI : μ.IsMulRightInvariant := R5bK.isMulRightInvariant_muK F
  haveI : μ.IsInvInvariant := R5bK.isInvInvariant_muK F
  let ι : R5bK.Kprod F →* GL (Fin 2) (InfiniteAdeleRing F) := R5bK.inclArch F
  have hιc : Continuous ι := R5bK.continuous_inclArch
  have hι : ∀ (κ : R5bK.Kprod F) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) :=
    fun κ w => R5bK.archComponent_inclArch κ w

  haveI := R5bC.t2Space_archMatrix' F
  haveI := R5bC.locallyCompactSpace_archGL F
  haveI := R5bC.secondCountableTopology_archGL F
  letI : MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing F)) := borel _
  haveI : BorelSpace (GL (Fin 2) (InfiniteAdeleRing F)) := ⟨rfl⟩
  obtain ⟨K₀⟩ := (inferInstance : Nonempty (TopologicalSpace.PositiveCompacts (GL (Fin 2) (InfiniteAdeleRing F))))
  let μa : Measure (GL (Fin 2) (InfiniteAdeleRing F)) := Measure.haarMeasure K₀
  haveI : μa.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure K₀
  haveI : μa.Regular := Measure.regular_haarMeasure
  haveI : μa.IsMulRightInvariant :=
    NumberField.AdelicHaar.isMulRightInvariant_of_isHaarMeasure_generalLinearGroup_infiniteAdeleRing F μa

  obtain ⟨E, hEfd, hYE, hEc, hEt, hEK⟩ : ∃ E : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ),
      FiniteDimensional ℂ ↥E ∧ Y ≤ E ∧ (∀ v ∈ E, Continuous v) ∧ E ≤ archCutSubmodule F tys ∧
      ∀ v ∈ E, ∀ κ : R5bK.Kprod F, (fun x => v (x * adelicArchGLIncl F (ι κ))) ∈ E := by
    let X := AdelicGL2 (𝓞 F) F
    let Sp : (X → ℂ) → Submodule ℂ (X → ℂ) := fun x =>
      Submodule.span ℂ (Set.range fun κ : R5bK.Kprod F => fun g : X => x (g * adelicArchGLIncl F (ι κ)))
    have hSp : ∀ x : X → ℂ, Continuous x → x ∈ archCutSubmodule F tys →
        FiniteDimensional ℂ ↥(Sp x) ∧ (∀ v ∈ Sp x, Continuous v) ∧ Sp x ≤ archCutSubmodule F tys ∧
        ∀ v ∈ Sp x, ∀ κ : R5bK.Kprod F, (fun g : X => v (g * adelicArchGLIncl F (ι κ))) ∈ Sp x :=
      fun x hxc hxt => AutomorphicForm.finiteDimensional_span_translates_of_mem_archCutSubmodule F ι hι tys x hxc hxt
    let b := Module.finBasis ℂ ↥Y
    let yv : Fin (Module.finrank ℂ ↥Y) → (X → ℂ) := fun i => (b i : X → ℂ)
    have hyvc : ∀ i, Continuous (yv i) := fun i => hYc _ (b i).2
    have hyvt : ∀ i, yv i ∈ archCutSubmodule F tys := fun i => hYt (b i).2
    let E : Submodule ℂ (X → ℂ) := ⨆ i, Sp (yv i)
    haveI : ∀ i, FiniteDimensional ℂ ↥(Sp (yv i)) := fun i => (hSp (yv i) (hyvc i) (hyvt i)).1
    have hEfd : FiniteDimensional ℂ ↥E := inferInstance
    let T : Submodule ℂ (X → ℂ) :=
      { carrier := {v | Continuous v ∧ v ∈ archCutSubmodule F tys ∧
          ∀ κ : R5bK.Kprod F, (fun g : X => v (g * adelicArchGLIncl F (ι κ))) ∈ E}
        add_mem' := by
          rintro v w ⟨hvc, hvt, hvs⟩ ⟨hwc, hwt, hws⟩
          exact ⟨hvc.add hwc, Submodule.add_mem _ hvt hwt, fun κ => by
            have h__af := E.add_mem (hvs κ) (hws κ)
            simp only [Pi.add_apply] at h__af ⊢
            exact h__af⟩
        zero_mem' := ⟨continuous_zero, Submodule.zero_mem _, fun κ => by
          have h__af := E.zero_mem
          simp only [Pi.zero_apply] at h__af ⊢
          exact h__af⟩
        smul_mem' := by
          rintro a v ⟨hvc, hvt, hvs⟩
          exact ⟨hvc.const_smul a, Submodule.smul_mem _ a hvt, fun κ => by
            have h__af := E.smul_mem a (hvs κ)
            simp only [Pi.smul_apply] at h__af ⊢
            exact h__af⟩ }
    have hET : E ≤ T := by
      refine iSup_le fun i => ?_
      intro v hv
      obtain ⟨-, hc, ht, hs⟩ := hSp (yv i) (hyvc i) (hyvt i)
      exact ⟨hc v hv, ht hv, fun κ => (le_iSup (fun i => Sp (yv i)) i) (hs v hv κ)⟩
    have hind : ∀ v ∈ E, Continuous v ∧ v ∈ archCutSubmodule F tys ∧
        ∀ κ : R5bK.Kprod F, (fun g : X => v (g * adelicArchGLIncl F (ι κ))) ∈ E :=
      fun v hv => hET hv
    have hyvE : ∀ i, yv i ∈ E := fun i =>
      (le_iSup (fun i => Sp (yv i)) i) (Submodule.subset_span ⟨1, by
        funext g
        show yv i (g * adelicArchGLIncl F (ι 1)) = yv i g
        rw [map_one, map_one, mul_one]⟩)
    refine ⟨E, hEfd, fun y hy => ?_, fun v hv => (hind v hv).1, fun v hv => (hind v hv).2.1,
      fun v hv κ => (hind v hv).2.2 κ⟩
    have hyeq : y = ∑ i, (b.repr ⟨y, hy⟩ i) • yv i := by
      have h0 := congrArg (fun z : ↥Y => (z : X → ℂ)) (b.sum_repr ⟨y, hy⟩)
      simpa only [Submodule.coe_sum, Submodule.coe_smul] using h0.symm
    rw [hyeq]
    exact E.sum_mem fun i _ => E.smul_mem _ (hyvE i)

  obtain ⟨e, heC, hecl, hefl, hedual, hety, hrep⟩ :=
    AutomorphicForm.exists_continuous_conj_invariant_integral_mul_apply_mul_eq_of_finiteDimensional_of_le_archCutSubmodule
      F μ ι hι tys E hEfd hEc hEt hEK

  obtain ⟨V, hV⟩ := (nhds (1 : GL (Fin 2) (InfiniteAdeleRing F))).exists_antitone_basis
  have hVmem : ∀ n, V n ∈ nhds (1 : GL (Fin 2) (InfiniteAdeleRing F)) := fun n => hV.mem n
  have hVshrink : ∀ W ∈ nhds (1 : GL (Fin 2) (InfiniteAdeleRing F)), ∀ᶠ n in Filter.atTop, V n ⊆ W :=
    fun W hW => hV.eventually_subset hW
  choose h hh using fun n =>
    AutomorphicForm.exists_isArchTestFactor_nonneg_and_tsupport_subset_and_conj_invariant_and_flat F σ (V n) (hVmem n)

  let avg : (GL (Fin 2) (InfiniteAdeleRing F) → ℂ) → (GL (Fin 2) (InfiniteAdeleRing F) → ℂ) := fun ψ y =>
    ∫ p : R5bK.Kprod F × R5bK.Kprod F, e p.1 * e p.2 * ψ ((ι p.1)⁻¹ * y * (ι p.2)⁻¹) ∂(μ.prod μ)
  have havg : ∀ ψ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ, IsArchTestFactor F ψ →
      (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
        ψ (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) = ψ x) →
      (∀ x : GL (Fin 2) (InfiniteAdeleRing F), ψ x = conj (ψ x⁻¹) *
        ((ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F x)) ^ (-σ) : ℝ) : ℂ)) →
      IsArchSphericalOfType F tys (avg ψ) ∧
      ∀ x : GL (Fin 2) (InfiniteAdeleRing F), avg ψ x = conj (avg ψ x⁻¹) *
        ((ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F x)) ^ (-σ) : ℝ) : ℂ) := by
    intro ψ hψt hψc hψf
    have hA := AutomorphicForm.isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule
      F μ ι hι tys e e heC heC ψ hψt
    have hB := AutomorphicForm.integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat
      F μ ι hι σ e hecl hefl ψ hψc hψf
    exact ⟨⟨hA.1, hA.2 hedual hety, hB.1⟩, hB.2⟩
  let fa₁ : ℕ → (GL (Fin 2) (InfiniteAdeleRing F) → ℂ) := fun n => avg (h n)
  have hsph : ∀ n, IsArchSphericalOfType F tys (fa₁ n) ∧
      ∀ x : GL (Fin 2) (InfiniteAdeleRing F), fa₁ n x = conj (fa₁ n x⁻¹) *
        ((ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F x)) ^ (-σ) : ℝ) : ℂ) :=
    fun n => havg (h n) (hh n).1 (hh n).2.2.2.2.1 (hh n).2.2.2.2.2

  obtain ⟨C, hC, hbridge⟩ :=
    AutomorphicForm.exists_pos_forall_rightConv_integral_prod_mul_indicator_eq_mul_integral_of_forall_integral_mul_apply_mul_eq
      F μ ι hιc hι μa U hUf hUo hUc

  have hψc : ∀ n, Continuous fun a => (h n a).re := fun n => Complex.continuous_re.comp (hTcont _ (hh n).1)
  have hψK : ∀ n, HasCompactSupport fun a => (h n a).re := fun n => (hh n).1.2.comp_left Complex.zero_re
  have hψ0 : ∀ n a, 0 ≤ (h n a).re := fun n a => ((hh n).2.1 a).2
  have hψ1 : ∀ n, 0 < (h n 1).re := fun n => (hh n).2.2.1
  have hψV : ∀ W ∈ nhds (1 : GL (Fin 2) (InfiniteAdeleRing F)), ∀ᶠ n in Filter.atTop,
      tsupport (fun a => (h n a).re) ⊆ W := fun W hW =>
    (hVshrink W hW).mono fun n hn =>
      ((closure_mono (Function.support_comp_subset Complex.zero_re (h n))).trans (hh n).2.2.2.1).trans hn
  let I : ℕ → ℝ := fun n => ∫ a, (h n a).re ∂μa
  have hI : ∀ n, 0 < I n := fun n => ApproxIdentity.integral_pos μa 1 (hψc n) (hψK n) (hψ0 n) (hψ1 n)
  let c : ℕ → ℝ := fun n => C⁻¹ * (I n)⁻¹

  let f : ℕ → (AdelicGL2 (𝓞 F) F → ℂ) := fun n g =>
    ((c n : ℂ) * fa₁ n (glArch (𝓞 F) F g)) *
      Set.indicator ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ)) (glFin (𝓞 F) F g)

  have hfaT : ∀ n, IsArchTestFactor F (fun x => (c n : ℂ) * fa₁ n x) := by
    intro n
    obtain ⟨⟨Φ, hΦ, hΦe⟩, hK⟩ := (hsph n).1.1
    exact ⟨⟨fun m => (c n : ℂ) * Φ m, contDiff_const.mul hΦ, fun g => by
      show (c n : ℂ) * fa₁ n g = (c n : ℂ) * Φ (archEntries F g)
      rw [hΦe]⟩, hK.mul_left⟩
  have hfaB : ∀ n, IsArchFactorBiFinite F tys (fun x => (c n : ℂ) * fa₁ n x) := by
    intro n
    obtain ⟨h1, h2⟩ := (hsph n).1.2.1
    exact ⟨(archFactorCutSubmodule F tys).smul_mem (c n : ℂ) h1,
      (archFactorDualCutSubmodule F tys).smul_mem (c n : ℂ) h2⟩
  have hfaC : ∀ n (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
      (fun x => (c n : ℂ) * fa₁ n x) (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) =
        (fun x => (c n : ℂ) * fa₁ n x) x := by
    intro n w k x
    show (c n : ℂ) * fa₁ n _ = (c n : ℂ) * fa₁ n x
    rw [(hsph n).1.2.2 w k x]

  have hNdet : ∀ y : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F y ∈ (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) →
      ideleNorm F (Matrix.GeneralLinearGroup.det y) =
        ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F (glArch (𝓞 F) F y))) := by
    rintro y ⟨u, hu, huy⟩
    have hu1 : glArch (𝓞 F) F u = 1 := (mem_finiteAdelicGL2Subgroup_iff F u).1 (hUf hu)
    have ha : adelicArchGLIncl F (glArch (𝓞 F) F y) = y * u⁻¹ := by
      have h := AutomorphicForm.C2ABridge.adelicArchGLIncl_glArch_of_glFin_eq_one F (y * u⁻¹)
        (by rw [map_mul, map_inv, huy, mul_inv_cancel])
      rwa [map_mul, map_inv, hu1, inv_one, mul_one] at h
    have hdu : ideleNorm F (Matrix.GeneralLinearGroup.det u) = 1 :=
      AutomorphicForm.C2ABridge.ideleNorm_det_eq_one_of_isCompact_of_mem F U hU u hu
    conv_lhs => rw [show y = adelicArchGLIncl F (glArch (𝓞 F) F y) * u by rw [ha, inv_mul_cancel_right]]
    rw [map_mul, ideleNorm_mul, hdu, mul_one]
  refine ⟨f, fun n => ⟨?_, ?_, ?_⟩, fun y hy g => ?_⟩
  ·
    exact ⟨fun x => (c n : ℂ) * fa₁ n x, _, hfaT n, hfin, fun g => rfl⟩
  ·
    exact ⟨fun x => (c n : ℂ) * fa₁ n x, hfaT n, hfaB n, hfaC n, fun g => rfl⟩
  ·
    funext y
    show conj (f n y⁻¹) * ((ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ (-σ) : ℝ) : ℂ) = f n y
    by_cases hy : glFin (𝓞 F) F y ∈ (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))
    · have hy' := hSinv y hy
      have hy'' : (glFin (𝓞 F) F y)⁻¹ ∈ (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) := by
        simpa only [map_inv] using hy'
      simp only [f, map_inv, Set.indicator_of_mem hy, Set.indicator_of_mem hy'', mul_one, map_mul,
        Complex.conj_ofReal]
      rw [(hsph n).2 (glArch (𝓞 F) F y), ← hNdet y hy]
      ring
    · have hy' : glFin (𝓞 F) F y⁻¹ ∉ (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) :=
        fun h' => hy (by simpa only [inv_inv] using hSinv y⁻¹ h')
      simp only [f, Set.indicator_of_notMem hy, Set.indicator_of_notMem hy', mul_zero, map_zero, zero_mul]
  ·
    have hyc : Continuous y := hYc y hy
    have hyU' : ∀ g' : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, y (g' * u) = y g' := fun g' u hu => hYU y hy g' u hu
    have hrep' : ∀ z : AdelicGL2 (𝓞 F) F, ∫ κ, e κ * y (z * adelicArchGLIncl F (ι κ)) ∂μ = y z :=
      fun z => hrep y (hYE hy) z
    have hφ : Continuous fun a : GL (Fin 2) (InfiniteAdeleRing F) => y (g * adelicArchGLIncl F a) :=
      hyc.comp ((continuous_const_mul g).comp R5bK.continuous_adelicArchGLIncl)
    have hstep1 : ∀ n, rightConv F y (f n) g =
        (c n : ℂ) * rightConv F y (fun y' => fa₁ n (glArch (𝓞 F) F y') *
          Set.indicator ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ)) (glFin (𝓞 F) F y')) g := by
      intro n
      simp only [rightConv, f]
      rw [← integral_const_mul]
      congr 1
      funext x
      ring
    have hstep2 : ∀ n, rightConv F y (fun y' => fa₁ n (glArch (𝓞 F) F y') *
          Set.indicator ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ)) (glFin (𝓞 F) F y')) g =
        C * ∫ a, y (g * adelicArchGLIncl F a) * h n a ∂μa :=
      fun n => hbridge e heC (h n) (hTcont _ (hh n).1) (hh n).1.2 (hh n).2.2.2.2.1 y hyc hyU' hrep' g
    have hstep3 : ∀ n, (∫ a, y (g * adelicArchGLIncl F a) * h n a ∂μa) =
        ∫ a, y (g * adelicArchGLIncl F a) * ((h n a).re : ℂ) ∂μa :=
      fun n => integral_congr_ae (Filter.Eventually.of_forall fun a => by
        show y (g * adelicArchGLIncl F a) * h n a = y (g * adelicArchGLIncl F a) * ((h n a).re : ℂ)
        rw [((hh n).2.1 a).1])
    have hlim := ApproxIdentity.tendsto_inv_integral_mul_integral_mul μa (1 : GL (Fin 2) (InfiniteAdeleRing F))
      hψc hψK hψ0 hψ1 hψV hφ
    simp only [map_one, mul_one] at hlim
    refine hlim.congr fun n => ?_
    have hC0 : (C : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hC.ne'
    have hI0 : ((I n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hI n).ne'
    have hIc : (∫ a, ((h n a).re : ℂ) ∂μa) = ((I n : ℝ) : ℂ) := integral_complex_ofReal
    rw [hstep1, hstep2, hstep3, hIc]
    show ((I n : ℝ) : ℂ)⁻¹ * _ = ((C⁻¹ * (I n)⁻¹ : ℝ) : ℂ) * ((C : ℂ) * _)
    rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_inv, mul_mul_mul_comm, inv_mul_cancel₀ hC0, one_mul]

end S_AutomorphicForm_exists_isLevelSphericalOfType_flat_tendsto_rightConv_of_finiteDimensional_of_isCompact
end P2MW
export P2MW.S_AutomorphicForm_exists_isLevelSphericalOfType_flat_tendsto_rightConv_of_finiteDimensional_of_isCompact (solution)
