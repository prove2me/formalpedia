-- Prove2me | solution 1 for AutomorphicForm.integrableOn_mul_finsum_sub_indicator_highSet_constantTerm_finsum_of_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/9e60d262-d907-5a3c-baec-417c7042842b

import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_NumberField_AdelicHeight
import Theorems.Thm_AutomorphicForm_adelicKernelLocalFiniteness
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_AutomorphicForm_ideleNorm_det_sigmaAdelicAct
import Theorems.Thm_NumberField_TateGlobal_exists_measure_fundamentalDomain_inter_ideleNorm_Icc_eq_mul_log
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_TateGlobal_exists_norm_apply_eq_ideleNorm_rpow
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integrableOn_mul_finsum_sub_indicator_highSet_constantTerm_finsum_of_hasCompactSupport
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped Topology Pointwise

noncomputable section

namespace R1HighSetFold

open AutomorphicForm

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem continuous_finsum_translate {Y : Type*} [TopologicalSpace Y]
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (S : Set (GL (Fin 2) L)) (g : AdelicGL2 (𝓞 L) L) (h : Y → AdelicGL2 (𝓞 L) L) (hh : Continuous h) :
    Continuous fun y => ∑ᶠ δ ∈ S, φ (g * globalPoints (𝓞 L) L δ * h y) := by
  classical
  refine continuous_iff_continuousAt.mpr fun y₀ => ?_
  obtain ⟨W, hWc, hWn⟩ := exists_compact_mem_nhds (h y₀)
  have hCW : IsCompact (tsupport φ * W⁻¹) := hφs.mul hWc.inv
  have hfin := AutomorphicForm.adelicKernelLocalFiniteness L (tsupport φ * W⁻¹) hCW g⁻¹ 1
  set T : Finset (GL (Fin 2) L) := hfin.toFinset with hT
  have key : ∀ y, h y ∈ W → ∀ δ, φ (g * globalPoints (𝓞 L) L δ * h y) ≠ 0 → δ ∈ T := by
    intro y hy δ hδ
    have hmem : g * globalPoints (𝓞 L) L δ * h y ∈ tsupport φ :=
      subset_tsupport _ (Function.mem_support.mpr hδ)
    simp only [hT, Set.Finite.mem_toFinset, Set.mem_setOf_eq, inv_inv, mul_one]
    refine Set.mem_mul.mpr ⟨g * globalPoints (𝓞 L) L δ * h y, hmem, (h y)⁻¹, Set.inv_mem_inv.mpr hy, ?_⟩
    group
  have hloc : ∀ y, h y ∈ W → (∑ᶠ δ ∈ S, φ (g * globalPoints (𝓞 L) L δ * h y)) =
      ∑ δ ∈ T, S.indicator (fun δ => φ (g * globalPoints (𝓞 L) L δ * h y)) δ := by
    intro y hy
    rw [finsum_mem_def]
    apply finsum_eq_sum_of_support_subset
    intro δ hδ
    rw [Function.mem_support] at hδ
    have h0 : φ (g * globalPoints (𝓞 L) L δ * h y) ≠ 0 := by
      intro h0
      apply hδ
      by_cases hδS : δ ∈ S
      · rw [Set.indicator_of_mem hδS, h0]
      · rw [Set.indicator_of_notMem hδS]
    exact Finset.mem_coe.mpr (key y hy δ h0)
  have hev : (fun y => ∑ᶠ δ ∈ S, φ (g * globalPoints (𝓞 L) L δ * h y)) =ᶠ[𝓝 y₀]
      fun y => ∑ δ ∈ T, S.indicator (fun δ => φ (g * globalPoints (𝓞 L) L δ * h y)) δ := by
    filter_upwards [hh.continuousAt.preimage_mem_nhds hWn] with y hy
    exact hloc y hy
  refine ContinuousAt.congr_of_eventuallyEq ?_ hev
  apply Continuous.continuousAt
  refine continuous_finsetSum _ fun δ _ => ?_
  by_cases hδS : δ ∈ S
  · simp only [Set.indicator_of_mem hδS]
    exact hφc.comp (continuous_const.mul hh)
  · simp only [Set.indicator_of_notMem hδS]
    exact continuous_const

theorem exists_card_le (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφs : HasCompactSupport φ)
    (x : AdelicGL2 (𝓞 L) L) :
    ∃ N : ℕ, ∀ (y : AdelicGL2 (𝓞 L) L) (s : Finset (GL (Fin 2) L)),
      (∀ δ ∈ s, x⁻¹ * globalPoints (𝓞 L) L δ * y ∈ tsupport φ) → s.card ≤ N := by
  classical
  have hC : IsCompact (tsupport φ * (tsupport φ)⁻¹) := hφs.mul hφs.inv
  have hfin := AutomorphicForm.adelicKernelLocalFiniteness L _ hC x x
  refine ⟨hfin.toFinset.card, fun y s hs => ?_⟩
  rcases s.eq_empty_or_nonempty with rfl | ⟨δ₀, hδ₀⟩
  · simp
  refine Finset.card_le_card_of_injOn (fun δ => δ * δ₀⁻¹) (fun δ hδ => ?_) ?_
  · simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    refine Set.mem_mul.mpr ⟨x⁻¹ * globalPoints (𝓞 L) L δ * y, hs δ hδ,
      (x⁻¹ * globalPoints (𝓞 L) L δ₀ * y)⁻¹, Set.inv_mem_inv.mpr (hs δ₀ hδ₀), ?_⟩
    simp only [map_mul, map_inv]
    group
  · intro a _ b _ hab
    exact mul_right_cancel hab

theorem exists_norm_finsum_le (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (x : AdelicGL2 (𝓞 L) L) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (S : Set (GL (Fin 2) L)) (y : AdelicGL2 (𝓞 L) L),
      ‖∑ᶠ δ ∈ S, φ (x⁻¹ * globalPoints (𝓞 L) L δ * y)‖ ≤ M := by
  classical
  obtain ⟨N, hN⟩ := exists_card_le φ hφs x
  obtain ⟨B, hB⟩ := hφc.bounded_above_of_compact_support hφs
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 1)
  refine ⟨N * B, by positivity, fun S y => ?_⟩
  have hfin : (S ∩ Function.support fun δ => φ (x⁻¹ * globalPoints (𝓞 L) L δ * y)).Finite := by
    apply Set.Finite.subset (AutomorphicForm.adelicKernelLocalFiniteness L _ hφs x y)
    intro δ hδ
    exact subset_tsupport _ hδ.2
  rw [finsum_mem_eq_sum _ hfin]
  have hcard : (hfin.toFinset.card : ℝ) ≤ N := by
    exact_mod_cast hN y _ fun δ hδ => subset_tsupport _ (hfin.mem_toFinset.mp hδ).2
  calc ‖∑ δ ∈ hfin.toFinset, φ (x⁻¹ * globalPoints (𝓞 L) L δ * y)‖
      ≤ ∑ δ ∈ hfin.toFinset, ‖φ (x⁻¹ * globalPoints (𝓞 L) L δ * y)‖ := norm_sum_le _ _
    _ ≤ ∑ _δ ∈ hfin.toFinset, B := Finset.sum_le_sum fun δ _ => hB _
    _ = hfin.toFinset.card * B := by simp
    _ ≤ N * B := by gcongr

theorem ideleNorm_one : NumberField.TateGlobal.ideleNorm L 1 = 1 := by
  simp [NumberField.TateGlobal.ideleNorm]

theorem ideleNorm_inv (u : (AdeleRing (𝓞 L) L)ˣ) :
    NumberField.TateGlobal.ideleNorm L u⁻¹ = (NumberField.TateGlobal.ideleNorm L u)⁻¹ := by
  simp [NumberField.TateGlobal.ideleNorm, map_inv]

theorem exists_shell (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφs : HasCompactSupport φ) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ ∀ g ∈ tsupport φ,
      NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b := by
  by_cases hne : (tsupport φ).Nonempty
  · have hcont := NumberField.TateGlobal.continuous_ideleNorm_det L
    obtain ⟨g₁, hg₁, hmin⟩ := hφs.exists_isMinOn hne hcont.continuousOn
    obtain ⟨g₂, hg₂, hmax⟩ := hφs.exists_isMaxOn hne hcont.continuousOn
    refine ⟨_, _, NumberField.TateGlobal.ideleNorm_pos _, isMinOn_iff.mp hmin g₂ hg₂,
      fun g hg => ⟨isMinOn_iff.mp hmin g hg, isMaxOn_iff.mp hmax g hg⟩⟩
  · exact ⟨1, 1, one_pos, le_rfl, fun g hg => (hne ⟨g, hg⟩).elim⟩

theorem det_centralScalar (z : (AdeleRing (𝓞 L) L)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z) = z * z := by
  show Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) z) = z * z
  rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, pow_two]

theorem det_unipotentGL2 (t : AdeleRing (𝓞 L) L) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 t) = 1 := by
  ext
  simp [Matrix.det_fin_two]

omit [NumberField K] in

theorem mem_shell_of_ne_zero (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) {a b : ℝ}
    (hab : ∀ g ∈ tsupport φ,
      NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b)
    (x : AdelicGL2 (𝓞 L) L) (δ : GL (Fin 2) L) (w : AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ)
    (hdet : Matrix.GeneralLinearGroup.det w = z * z * Matrix.GeneralLinearGroup.det x)
    (h : φ (x⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ w) ≠ 0) :
    NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc (Real.sqrt a) (Real.sqrt b) := by
  have hmem := hab _ (subset_tsupport _ (Function.mem_support.mpr h))
  rw [map_mul, map_mul, map_inv, NumberField.TateGlobal.ideleNorm_mul, NumberField.TateGlobal.ideleNorm_mul,
    AutomorphicForm.ideleNorm_det_sigmaAdelicAct K L D σ w, AutomorphicForm.ideleNorm_det_globalPoints,
    ideleNorm_inv, hdet, NumberField.TateGlobal.ideleNorm_mul, NumberField.TateGlobal.ideleNorm_mul] at hmem
  have hx := NumberField.TateGlobal.ideleNorm_pos (Matrix.GeneralLinearGroup.det x)
  have hz := NumberField.TateGlobal.ideleNorm_pos z
  have hsq : (NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det x))⁻¹ * 1 *
      (NumberField.TateGlobal.ideleNorm L z * NumberField.TateGlobal.ideleNorm L z *
        NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det x)) =
      NumberField.TateGlobal.ideleNorm L z ^ 2 := by
    field_simp
  rw [hsq] at hmem
  constructor
  · calc Real.sqrt a ≤ Real.sqrt (NumberField.TateGlobal.ideleNorm L z ^ 2) := Real.sqrt_le_sqrt hmem.1
      _ = NumberField.TateGlobal.ideleNorm L z := Real.sqrt_sq hz.le
  · calc NumberField.TateGlobal.ideleNorm L z = Real.sqrt (NumberField.TateGlobal.ideleNorm L z ^ 2) :=
          (Real.sqrt_sq hz.le).symm
      _ ≤ Real.sqrt b := Real.sqrt_le_sqrt hmem.2

theorem continuous_centralScalar : Continuous (centralScalar (𝓞 L) L) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · have : (Units.val ∘ centralScalar (𝓞 L) L) =
        fun z : (AdeleRing (𝓞 L) L)ˣ => Matrix.diagonal fun _ : Fin 2 => (z : AdeleRing (𝓞 L) L) := by
      funext z
      rfl
    rw [this]
    exact Continuous.matrix_diagonal (continuous_pi fun _ => Units.continuous_val)
  · have : (fun z : (AdeleRing (𝓞 L) L)ˣ => ((centralScalar (𝓞 L) L z)⁻¹ : AdelicGL2 (𝓞 L) L).val) =
        fun z : (AdeleRing (𝓞 L) L)ˣ => Matrix.diagonal fun _ : Fin 2 => ((z⁻¹ : (AdeleRing (𝓞 L) L)ˣ) :
          AdeleRing (𝓞 L) L) := by
      funext z
      rw [← map_inv]
      rfl
    rw [this]
    exact Continuous.matrix_diagonal (continuous_pi fun _ => Units.continuous_coe_inv)

theorem exists_norm_char_le (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    {a b : ℝ} (ha : 0 < a) :
    ∃ Ξ : ℝ, 0 ≤ Ξ ∧ ∀ z : (AdeleRing (𝓞 L) L)ˣ, NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc a b →
      ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ ≤ Ξ := by

  let μ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ := ξL.comp (Subgroup.topEquiv (G := (AdeleRing (𝓞 L) L)ˣ)).symm.toMonoidHom
  have hμ : ∀ z, μ z = ξL ⟨z, Subgroup.mem_top z⟩ := fun z => rfl
  have hclass : AutomorphicForm.IsIdeleClassChar (𝓞 L) L μ := by
    intro u
    rw [hμ]
    exact hξt _ ⟨u, rfl⟩
  have hcont : Continuous μ := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · exact hξc
    · have : (fun z : (AdeleRing (𝓞 L) L)ˣ => ((μ z)⁻¹ : ℂˣ).val) =
          fun z => ((ξL ⟨z⁻¹, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) := by
        funext z
        rw [← map_inv, hμ]
      rw [this]
      exact hξc.comp continuous_inv
  obtain ⟨s, hs⟩ := NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow L μ hclass hcont
  have hm : 0 < max a b := lt_max_of_lt_left ha
  refine ⟨a ^ s + (max a b) ^ s, by positivity, fun z hz => ?_⟩
  rw [← hμ, hs z]
  have hn := NumberField.TateGlobal.ideleNorm_pos z
  rcases le_or_gt 0 s with hs0 | hs0
  · calc NumberField.TateGlobal.ideleNorm L z ^ s ≤ (max a b) ^ s :=
          Real.rpow_le_rpow hn.le (hz.2.trans (le_max_right a b)) hs0
      _ ≤ a ^ s + (max a b) ^ s := le_add_of_nonneg_left (by positivity)
  · calc NumberField.TateGlobal.ideleNorm L z ^ s ≤ a ^ s :=
          Real.rpow_le_rpow_of_nonpos ha hz.1 hs0.le
      _ ≤ a ^ s + (max a b) ^ s := le_add_of_nonneg_right (by positivity)

end R1HighSetFold

open R1HighSetFold AutomorphicForm in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (ΦL : Set (AdelicGL2 (𝓞 L) L))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (I J : Set (GL (Fin 2) L)) (R : ℝ) (x : AdelicGL2 (𝓞 L) L) :
    IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ =>
        ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ((∑ᶠ δ ∈ I,
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ J,
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ΩL νZL := by
  classical

  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := NumberField.AdeleRing.secondCountableTopology L
  haveI : FirstCountableTopology (AdeleRing (𝓞 L) L)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := AdeleRing (𝓞 L) L)).symm.isInducing.firstCountableTopology
  haveI : FirstCountableTopology (AdeleRing (𝓞 L) L)ˣ :=
    Units.isInducing_embedProduct.firstCountableTopology

  letI mA : MeasurableSpace (AdeleRing (𝓞 L) L) := adeleBorel (𝓞 L) L
  haveI : BorelSpace (AdeleRing (𝓞 L) L) := borelSpace_adeleBorel (𝓞 L) L

  set Aset : Set (GL (Fin 2) L) := I with hAset
  set Bset : Set (GL (Fin 2) L) := J with hBset
  set ν : Measure (AdeleRing (𝓞 L) L) :=
    @ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L) with hν
  haveI hνfin : IsFiniteMeasure ν := by rw [hν]; infer_instance
  set ξ : (AdeleRing (𝓞 L) L)ˣ → ℂ := fun z => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) with hξ
  set ι := AutomorphicForm.globalPoints (𝓞 L) L with hι
  set σA := AutomorphicForm.sigmaAdelicAct K L D σ with hσA
  set zc := AutomorphicForm.centralScalar (𝓞 L) L with hzc
  set inner : AdelicGL2 (𝓞 L) L → ℂ := fun y => ∑ᶠ δ ∈ Bset, φ (x⁻¹ * ι δ * σA y) with hinner
  set U : (AdeleRing (𝓞 L) L)ˣ → ℂ := fun z => ∑ᶠ δ ∈ Aset, φ (x⁻¹ * ι δ * σA (zc z * x)) with hU
  set CT : (AdeleRing (𝓞 L) L)ˣ → ℂ := fun z => ∫ t, inner (AutomorphicForm.unipotentGL2 t * (zc z * x)) ∂ν
    with hCT
  set E : Set (AdeleRing (𝓞 L) L)ˣ :=
    (fun z => zc z * x) ⁻¹' AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R) with hE
  set F : (AdeleRing (𝓞 L) L)ˣ → ℂ := fun z => ξ z * (U z - E.indicator CT z) with hF

  show IntegrableOn F ΩL νZL

  have hzc : Continuous zc := continuous_centralScalar
  have hσAc : Continuous σA := AutomorphicForm.continuous_sigmaAdelicAct K L D σ
  have hn : Continuous fun t : AdeleRing (𝓞 L) L => AutomorphicForm.unipotentGL2 t :=
    AutomorphicForm.continuous_unipotentGL2

  have hUc : Continuous U :=
    continuous_finsum_translate φ hφc hφs Aset x⁻¹ (fun z => σA (zc z * x))
      (hσAc.comp (hzc.mul continuous_const))
  have hin_t : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      Continuous fun t : AdeleRing (𝓞 L) L => inner (AutomorphicForm.unipotentGL2 t * (zc z * x)) := fun z =>
    continuous_finsum_translate φ hφc hφs Bset x⁻¹ (fun t => σA (AutomorphicForm.unipotentGL2 t * (zc z * x)))
      (hσAc.comp (hn.mul continuous_const))
  have hin_z : ∀ t : AdeleRing (𝓞 L) L,
      Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => inner (AutomorphicForm.unipotentGL2 t * (zc z * x)) := fun t =>
    continuous_finsum_translate φ hφc hφs Bset x⁻¹ (fun z => σA (AutomorphicForm.unipotentGL2 t * (zc z * x)))
      (hσAc.comp (continuous_const.mul (hzc.mul continuous_const)))

  obtain ⟨M, hM0, hM⟩ := exists_norm_finsum_le φ hφc hφs x
  have hin_bd : ∀ (z : (AdeleRing (𝓞 L) L)ˣ) (t : AdeleRing (𝓞 L) L),
      ‖inner (AutomorphicForm.unipotentGL2 t * (zc z * x))‖ ≤ M := fun z t => hM Bset _
  have hU_bd : ∀ z, ‖U z‖ ≤ M := fun z => hM Aset _
  have hCT_bd : ∀ z, ‖CT z‖ ≤ M * ν.real Set.univ := fun z =>
    norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall (hin_bd z))
  have hCTc : Continuous CT := by
    refine continuous_of_dominated (bound := fun _ => M) (fun z => (hin_t z).aestronglyMeasurable)
      (fun z => Filter.Eventually.of_forall (hin_bd z)) (integrable_const M)
      (Filter.Eventually.of_forall hin_z)

  have hEm : MeasurableSet E := by
    refine (IsOpen.preimage (hzc.mul continuous_const) ?_).measurableSet
    exact isOpen_lt continuous_const (NumberField.AdelicHeight.continuous_adelicHeight L)
  have hFm : Measurable F :=
    hξc.measurable.mul (hUc.measurable.sub (hCTc.measurable.indicator hEm))

  obtain ⟨a, b, ha, hab, hsupp⟩ := exists_shell φ hφs
  set shell : Set (AdeleRing (𝓞 L) L)ˣ :=
    {z | NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc (Real.sqrt a) (Real.sqrt b)} with hshell
  have hshellm : MeasurableSet shell :=
    measurableSet_Icc.preimage (NumberField.TateGlobal.continuous_ideleNorm L).measurable
  have hdet1 : ∀ z : (AdeleRing (𝓞 L) L)ˣ, Matrix.GeneralLinearGroup.det (zc z * x) =
      z * z * Matrix.GeneralLinearGroup.det x := fun z => by
    rw [map_mul, det_centralScalar]
  have hdet2 : ∀ (z : (AdeleRing (𝓞 L) L)ˣ) (t : AdeleRing (𝓞 L) L),
      Matrix.GeneralLinearGroup.det (AutomorphicForm.unipotentGL2 t * (zc z * x)) =
        z * z * Matrix.GeneralLinearGroup.det x := fun z t => by
    rw [map_mul, det_unipotentGL2, one_mul, hdet1]
  have hU0 : ∀ z, z ∉ shell → U z = 0 := by
    intro z hz
    apply finsum_mem_of_eqOn_zero
    intro δ _
    by_contra h
    exact hz (mem_shell_of_ne_zero D σ φ hsupp x δ (zc z * x) z (hdet1 z) h)
  have hin0 : ∀ z, z ∉ shell → ∀ t, inner (AutomorphicForm.unipotentGL2 t * (zc z * x)) = 0 := by
    intro z hz t
    apply finsum_mem_of_eqOn_zero
    intro δ _
    by_contra h
    exact hz (mem_shell_of_ne_zero D σ φ hsupp x δ _ z (hdet2 z t) h)
  have hCT0 : ∀ z, z ∉ shell → CT z = 0 := by
    intro z hz
    show (∫ t, inner (AutomorphicForm.unipotentGL2 t * (zc z * x)) ∂ν) = 0
    simp_rw [hin0 z hz]
    exact integral_zero _ _
  have hF0 : ∀ z, z ∉ shell → F z = 0 := by
    intro z hz
    show ξ z * (U z - E.indicator CT z) = 0
    rw [hU0 z hz, Set.indicator_apply_eq_zero.mpr fun _ => hCT0 z hz, sub_zero, mul_zero]

  obtain ⟨Ξ, hΞ0, hΞ⟩ := exists_norm_char_le (L := L) ξL hξc hξt (b := Real.sqrt b) (Real.sqrt_pos.mpr ha)
  have hF_bd : ∀ z ∈ shell, ‖F z‖ ≤ Ξ * (M + M * ν.real Set.univ) := by
    intro z hz
    show ‖ξ z * (U z - E.indicator CT z)‖ ≤ Ξ * (M + M * ν.real Set.univ)
    rw [norm_mul]
    refine mul_le_mul (hΞ z hz) ?_ (norm_nonneg _) hΞ0
    calc ‖U z - E.indicator CT z‖ ≤ ‖U z‖ + ‖E.indicator CT z‖ := norm_sub_le _ _
      _ ≤ M + M * ν.real Set.univ :=
        add_le_add (hU_bd z) (le_trans (norm_indicator_le_norm_self CT z) (hCT_bd z))

  obtain ⟨C, hC0, hCtop, hC⟩ :=
    NumberField.TateGlobal.exists_measure_fundamentalDomain_inter_ideleNorm_Icc_eq_mul_log L νZL
  have hfin : νZL (ΩL ∩ shell) ≠ ⊤ := by
    rw [hC ΩL hΩL (Real.sqrt a) (Real.sqrt b) (Real.sqrt_pos.mpr ha) (Real.sqrt_le_sqrt hab)]
    exact ENNReal.mul_ne_top hCtop ENNReal.ofReal_ne_top

  have hnull : NullMeasurableSet (ΩL ∩ shell) νZL :=
    hΩL.nullMeasurableSet.inter hshellm.nullMeasurableSet
  have h1 : IntegrableOn F (ΩL ∩ shell) νZL := by
    refine Measure.integrableOn_of_bounded (M := Ξ * (M + M * ν.real Set.univ)) hfin hFm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem₀ hnull] with z hz
    exact hF_bd z hz.2
  refine h1.of_ae_diff_eq_zero hΩL.nullMeasurableSet (Filter.Eventually.of_forall fun z hz => ?_)
  exact hF0 z fun hs => hz.2 ⟨hz.1, hs⟩

end
end S_AutomorphicForm_integrableOn_mul_finsum_sub_indicator_highSet_constantTerm_finsum_of_hasCompactSupport
end P2MW
export P2MW.S_AutomorphicForm_integrableOn_mul_finsum_sub_indicator_highSet_constantTerm_finsum_of_hasCompactSupport (solution)
