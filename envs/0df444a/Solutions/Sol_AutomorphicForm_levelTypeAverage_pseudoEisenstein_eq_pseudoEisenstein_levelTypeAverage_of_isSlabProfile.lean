-- Prove2me | solution 1 for AutomorphicForm.levelTypeAverage_pseudoEisenstein_eq_pseudoEisenstein_levelTypeAverage_of_isSlabProfile
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/aaf0dcb3-8961-5b7e-9500-4dc81a8d29aa

import Theorems.Thm_AutomorphicForm_finite_support_pseudoEisenstein_summand
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_mul_of_mem_adelicMaximalCompact
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_levelTypeAverage_pseudoEisenstein_eq_pseudoEisenstein_levelTypeAverage_of_isSlabProfile
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open AutomorphicForm NumberField.AdelicHeight
open scoped ENNReal

theorem solution
    (K : Type) [Field K] [NumberField K]
    (Z : Subgroup (AdeleRing (𝓞 K) K)ˣ) (ξ : Z →* ℂˣ) (hξu : ∀ z : Z, ‖((ξ z : ℂˣ) : ℂ)‖ = 1)
    (κ : ↥(adelicMaximalCompact K) → ℂ) (_hκ : Continuous κ)
    (P : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ))
    (_hP : ∀ (φ : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K),
      P φ g = ∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))
    (ψ : AdelicGL2 (𝓞 K) K → ℂ) (_hψ : AutomorphicForm.IsSlabProfile K Z ξ ψ)
    (g : AdelicGL2 (𝓞 K) K) :
    AutomorphicForm.pseudoEisenstein K (P ψ) g = P (AutomorphicForm.pseudoEisenstein K ψ) g := by
  classical
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  set μK := maximalCompactHaar K with hμK

  have hdetc : Continuous fun k : adelicMaximalCompact K =>
      NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 K) K)) :=
    (NumberField.TateGlobal.continuous_ideleNorm_det K).comp continuous_subtype_val
  obtain ⟨k₀⟩ := (inferInstance : Nonempty (adelicMaximalCompact K))
  obtain ⟨kmin, -, hmin⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty) hdetc.continuousOn
  obtain ⟨kmax, -, hmax⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty) hdetc.continuousOn
  set m := NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (kmin : AdelicGL2 (𝓞 K) K)) with hm
  set M := NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (kmax : AdelicGL2 (𝓞 K) K)) with hM
  have hm0 : 0 < m := NumberField.TateGlobal.ideleNorm_pos _
  have hmM : ∀ k : adelicMaximalCompact K,
      NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 K) K)) ∈ Set.Icc m M :=
    fun k => ⟨hmin (Set.mem_univ k), hmax (Set.mem_univ k)⟩

  have hbdd : ∀ h : AdelicGL2 (𝓞 K) K, ∃ C : ℝ, ∀ k : adelicMaximalCompact K, ‖ψ (h * (k : AdelicGL2 (𝓞 K) K))‖ ≤ C := by
    intro h
    have hd : 0 < NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det h) :=
      NumberField.TateGlobal.ideleNorm_pos _
    obtain ⟨C, hC⟩ := _hψ.bounded_on_slab
      (NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det h) * m)
      (NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det h) * M) (mul_pos hd hm0)
    refine ⟨C, fun k => hC _ ?_⟩
    rw [map_mul, NumberField.TateGlobal.ideleNorm_mul]
    exact ⟨mul_le_mul_of_nonneg_left (hmM k).1 hd.le, mul_le_mul_of_nonneg_left (hmM k).2 hd.le⟩
  have hψm : Measurable ψ := _hψ.measurable
  have hκi : Integrable (fun k : adelicMaximalCompact K => ‖κ k‖) μK :=
    _hκ.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

  have hint : ∀ h : AdelicGL2 (𝓞 K) K, Integrable (fun k : adelicMaximalCompact K => κ k * ψ (h * (k : AdelicGL2 (𝓞 K) K))) μK := by
    intro h
    obtain ⟨C, hC⟩ := hbdd h
    have hmeas : AEStronglyMeasurable (fun k : adelicMaximalCompact K => κ k * ψ (h * (k : AdelicGL2 (𝓞 K) K))) μK :=
      _hκ.aestronglyMeasurable.mul
        (hψm.comp ((continuous_const.mul continuous_subtype_val).measurable)).aestronglyMeasurable
    refine Integrable.mono' (hκi.mul_const (max C 0)) hmeas (Filter.Eventually.of_forall fun k => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left ((hC k).trans (le_max_left _ _)) (norm_nonneg _)
  have hΨr_int : ∀ h : AdelicGL2 (𝓞 K) K, Integrable (fun k : adelicMaximalCompact K => ‖ψ (h * (k : AdelicGL2 (𝓞 K) K))‖ * ‖κ k‖) μK := fun h => by
    have := (hint h).norm
    simpa only [norm_mul, mul_comm] using this
  have hΨr_nn : ∀ h : AdelicGL2 (𝓞 K) K, 0 ≤ ∫ k, ‖ψ (h * (k : AdelicGL2 (𝓞 K) K))‖ * ‖κ k‖ ∂μK := fun h =>
    integral_nonneg fun k => mul_nonneg (norm_nonneg _) (norm_nonneg _)

  set Ψ : AdelicGL2 (𝓞 K) K → ℂ := fun h => (((∫ k, ‖ψ (h * (k : AdelicGL2 (𝓞 K) K))‖ * ‖κ k‖ ∂μK) : ℝ) : ℂ) with hΨ
  have hΨprof : IsSlabProfile K Z (1 : Z →* ℂˣ) Ψ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hsm : StronglyMeasurable (Function.uncurry fun (h : AdelicGL2 (𝓞 K) K) (k : adelicMaximalCompact K) =>
          ‖ψ (h * (k : AdelicGL2 (𝓞 K) K))‖ * ‖κ k‖) :=
        (((hψm.comp (continuous_fst.mul (continuous_subtype_val.comp continuous_snd)).measurable).norm).mul
          ((_hκ.measurable.comp measurable_snd).norm)).stronglyMeasurable
      exact Complex.measurable_ofReal.comp hsm.integral_prod_right.measurable
    · intro x h
      simp only [hΨ, mul_assoc, _hψ.unipotent_mul]
    · intro γ hγ h
      simp only [hΨ, mul_assoc, _hψ.borel_mul γ hγ]
    · intro z h
      simp only [hΨ, mul_assoc, _hψ.central_transform, norm_mul, hξu, one_mul, MonoidHom.one_apply,
        Units.val_one]
    · intro d₁ d₂ hd₁
      obtain ⟨C, hC⟩ := _hψ.bounded_on_slab (d₁ * m) (d₂ * M) (mul_pos hd₁ hm0)
      refine ⟨max C 0 * ∫ k, ‖κ k‖ ∂μK, fun h hh => ?_⟩
      simp only [hΨ, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hΨr_nn h)]
      calc (∫ k, ‖ψ (h * (k : AdelicGL2 (𝓞 K) K))‖ * ‖κ k‖ ∂μK) ≤ ∫ k, max C 0 * ‖κ k‖ ∂μK := by
            refine integral_mono (hΨr_int h) (hκi.const_mul _) fun k => ?_
            refine mul_le_mul_of_nonneg_right ((hC _ ?_).trans (le_max_left _ _)) (norm_nonneg _)
            rw [map_mul, NumberField.TateGlobal.ideleNorm_mul]
            exact ⟨mul_le_mul hh.1 (hmM k).1 hm0.le (hd₁.le.trans hh.1),
              mul_le_mul hh.2 (hmM k).2 (NumberField.TateGlobal.ideleNorm_pos _).le
                (hd₁.le.trans (hh.1.trans hh.2))⟩
        _ = max C 0 * ∫ k, ‖κ k‖ ∂μK := integral_const_mul _ _
    · obtain ⟨a, b, ha, hband⟩ := _hψ.height_band
      refine ⟨a, b, ha, fun h hh => ?_⟩
      have hex : ∃ k : adelicMaximalCompact K, ψ (h * (k : AdelicGL2 (𝓞 K) K)) ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        apply hh
        simp only [hΨ]
        rw [integral_eq_zero_of_ae (Filter.Eventually.of_forall fun k => ?_), Complex.ofReal_zero]
        show ‖ψ (h * (k : AdelicGL2 (𝓞 K) K))‖ * ‖κ k‖ = (0 : adelicMaximalCompact K → ℝ) k
        rw [hcon k, norm_zero, zero_mul, Pi.zero_apply]
      obtain ⟨k, hψk⟩ := hex
      have hhk := hband _ hψk
      rwa [NumberField.AdelicHeight.adelicHeight_mul_of_mem_adelicMaximalCompact K h (k : AdelicGL2 (𝓞 K) K) k.2] at hhk

  have hfinB := AutomorphicForm.finite_support_pseudoEisenstein_summand K Z 1 Ψ hΨprof g
  set B : Finset K := hfinB.toFinset with hB
  have hBout : ∀ β : K, β ∉ B → Ψ ((adelicWeyl (𝓞 K) K * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β)) * g) = 0 := fun β hβ => by
    by_contra hne
    exact hβ (hfinB.mem_toFinset.2 hne)
  have hzero : ∀ β : K, β ∉ B → ∀ᵐ k ∂μK, κ k * ψ ((adelicWeyl (𝓞 K) K * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β)) * g * (k : AdelicGL2 (𝓞 K) K)) = 0 := by
    intro β hβ
    have h0 : (∫ k, ‖ψ ((adelicWeyl (𝓞 K) K * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β)) * g * (k : AdelicGL2 (𝓞 K) K))‖ * ‖κ k‖ ∂μK) = 0 := by
      have := hBout β hβ
      simp only [hΨ, Complex.ofReal_eq_zero] at this
      exact this
    have hae := (integral_eq_zero_iff_of_nonneg (fun k => mul_nonneg (norm_nonneg _) (norm_nonneg _)) (hΨr_int _)).1 h0
    filter_upwards [hae] with k hk
    have : ‖κ k * ψ ((adelicWeyl (𝓞 K) K * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β)) * g * (k : AdelicGL2 (𝓞 K) K))‖ = 0 := by rw [norm_mul, mul_comm]; exact hk
    exact norm_eq_zero.1 this
  haveI : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := K)
  have hzero' : ∀ᵐ k ∂μK, ∀ β : K, β ∉ B → κ k * ψ ((adelicWeyl (𝓞 K) K * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β)) * g * (k : AdelicGL2 (𝓞 K) K)) = 0 := by
    rw [ae_all_iff]
    intro β
    by_cases hβ : β ∈ B
    · exact Filter.Eventually.of_forall fun k h => (h hβ).elim
    · exact (hzero β hβ).mono fun k hk _ => hk
  have hPout : ∀ β : K, β ∉ B → P ψ ((adelicWeyl (𝓞 K) K * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β)) * g) = 0 := by
    intro β hβ
    rw [_hP]
    exact integral_eq_zero_of_ae (hzero β hβ)

  have hRHS : P (AutomorphicForm.pseudoEisenstein K ψ) g =
      ∫ k, κ k * (ψ (g * (k : AdelicGL2 (𝓞 K) K)) + ∑' β : K, ψ ((adelicWeyl (𝓞 K) K * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β)) * (g * (k : AdelicGL2 (𝓞 K) K)))) ∂μK := by
    rw [_hP]
    rfl
  have hsplit : ∀ᵐ k ∂μK, κ k * (ψ (g * (k : AdelicGL2 (𝓞 K) K)) + ∑' β : K, ψ ((adelicWeyl (𝓞 K) K * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β)) * (g * (k : AdelicGL2 (𝓞 K) K)))) =
      κ k * ψ (g * (k : AdelicGL2 (𝓞 K) K)) + ∑ β ∈ B, κ k * ψ ((adelicWeyl (𝓞 K) K * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β)) * g * (k : AdelicGL2 (𝓞 K) K)) := by
    filter_upwards [hzero'] with k hk
    rw [mul_add]
    congr 1
    by_cases hκk : κ k = 0
    · simp [hκk]
    · rw [tsum_eq_sum (s := B) (fun β hβ => ?_), Finset.mul_sum]
      · exact Finset.sum_congr rfl fun β _ => by simp only [mul_assoc]
      · have h := hk β hβ
        rw [mul_assoc] at h
        exact (mul_eq_zero.1 h).resolve_left hκk
  have hintβ : ∀ β : K, Integrable (fun k : adelicMaximalCompact K => κ k * ψ ((adelicWeyl (𝓞 K) K * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β)) * g * (k : AdelicGL2 (𝓞 K) K))) μK :=
    fun β => hint _
  rw [hRHS, integral_congr_ae hsplit, integral_add (hint g) (integrable_finsetSum _ fun β _ => hintβ β),
    integral_finsetSum _ fun β _ => hintβ β, pseudoEisenstein_apply]
  congr 1
  · rw [_hP]
  · rw [tsum_eq_sum (s := B) (fun β hβ => hPout β hβ)]
    exact Finset.sum_congr rfl fun β _ => by rw [_hP]

end S_AutomorphicForm_levelTypeAverage_pseudoEisenstein_eq_pseudoEisenstein_levelTypeAverage_of_isSlabProfile
end P2MW
export P2MW.S_AutomorphicForm_levelTypeAverage_pseudoEisenstein_eq_pseudoEisenstein_levelTypeAverage_of_isSlabProfile (solution)
