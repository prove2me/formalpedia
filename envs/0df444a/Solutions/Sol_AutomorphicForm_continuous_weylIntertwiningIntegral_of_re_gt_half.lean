-- Prove2me | solution 1 for AutomorphicForm.continuous_weylIntertwiningIntegral_of_re_gt_half
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/66f02132-bb2f-563a-8fe5-fb55b74edbb7

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicHeight
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Theorems.Thm_AutomorphicForm_weylIntertwiningIntegrand_integrable_of_re_gt_half
import Theorems.Thm_AutomorphicForm_exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection
import Theorems.Thm_NumberField_AdelicHeight_exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact
import Theorems.Thm_AutomorphicForm_isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_continuous_weylIntertwiningIntegral_of_re_gt_half
p2m_attr_erase "instance" "instCountableOfNumberField_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicHeight
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_continuous_weylIntertwiningIntegral_of_re_gt_half.AutomorphicForm"
open scoped NNReal

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsInducedSection AdelicGL2 IsUnitaryChar unipotentGL2 etaFst etaSnd adelicWeyl weylIntertwiningIntegral weylIntertwiningIntegrand_integrable_of_re_gt_half exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow"
namespace ContM
p2m_open "AutomorphicForm"

open IsDedekindDomain

variable (F : Type) [Field F] [NumberField F]

theorem countable_ideal : Countable (Ideal (𝓞 F)) := by
  have h : (Set.univ : Set (Ideal (𝓞 F))) = ⋃ n : ℕ, {I : Ideal (𝓞 F) | Ideal.absNorm I = n} := by
    ext I
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_setOf_eq, true_iff]
    exact ⟨_, rfl⟩
  rw [← Set.countable_univ_iff, h]
  exact Set.countable_iUnion fun n => (Ideal.finite_setOf_absNorm_eq n).countable

theorem countable_heightOneSpectrum : Countable (HeightOneSpectrum (𝓞 F)) := by
  haveI := countable_ideal F
  exact Function.Injective.countable fun v w (h : v.asIdeal = w.asIdeal) => HeightOneSpectrum.ext h

theorem firstCountableTopology_finiteAdeleRing : FirstCountableTopology (FiniteAdeleRing (𝓞 F) F) := by
  haveI := countable_heightOneSpectrum F
  refine ⟨fun x => ?_⟩

  set S : Set (HeightOneSpectrum (𝓞 F)) := {v | x v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))}
    with hS
  have hSc : Filter.cofinite ≤ Filter.principal S := Filter.le_principal_iff.2 x.2
  let x' : RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (Filter.principal S) :=
    ⟨fun v => x v, Filter.eventually_principal.2 fun v hv => hv⟩
  have hx : RestrictedProduct.inclusion (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) hSc x' = x := rfl
  have hopen : ∀ v : HeightOneSpectrum (𝓞 F), IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    fun v => Valued.isOpen_valuationSubring _
  haveI : (nhds x').IsCountablyGenerated := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.nhds_eq_comap x']
    exact Filter.comap.isCountablyGenerated _ _
  have h := RestrictedProduct.nhds_eq_map_inclusion hopen hSc x'
  have key := h.symm ▸ Filter.map.isCountablyGenerated (nhds x')
    (RestrictedProduct.inclusion (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) hSc)
  rw [← hx]
  exact key

theorem firstCountableTopology_adeleRing : FirstCountableTopology (AdeleRing (𝓞 F) F) := by
  haveI := firstCountableTopology_finiteAdeleRing F
  haveI : FirstCountableTopology (InfiniteAdeleRing F) :=
    inferInstanceAs (FirstCountableTopology ((w : InfinitePlace F) → w.Completion))
  exact inferInstanceAs (FirstCountableTopology (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

theorem firstCountableTopology_adelicGL2 : FirstCountableTopology (AdelicGL2 (𝓞 F) F) := by
  haveI := firstCountableTopology_adeleRing F
  haveI : FirstCountableTopology (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) :=
    inferInstanceAs (FirstCountableTopology (Fin 2 → Fin 2 → AdeleRing (𝓞 F) F))
  haveI : FirstCountableTopology (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))ᵐᵒᵖ :=
    ⟨fun m => by
      rw [← MulOpposite.op_unop m, ← MulOpposite.map_op_nhds]
      exact Filter.map.isCountablyGenerated _ _⟩
  refine ⟨fun u => ?_⟩
  rw [Units.isEmbedding_embedProduct.nhds_eq_comap u]
  exact Filter.comap.isCountablyGenerated _ _

end AutomorphicForm.ContM

theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (s : ℂ) (_hs : 1 / 2 < s.re) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφc : Continuous φ),
    letI := adeleBorel (𝓞 F) F
    Continuous (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ) := by
  intro α hα μ ν hμ hν s hs φ hφ hφc
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  set p : ℝ := s.re + 1 / 2 with hp
  have hp0 : 0 ≤ p := by rw [hp]; linarith

  obtain ⟨Cφ, hCφ⟩ :=
    AutomorphicForm.exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection F hα μ ν hμ hν s φ hφ hφc

  have h1 : IsUnitaryChar (𝓞 F) F (1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) := fun x => by simp
  have hsph := AutomorphicForm.isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow F hα (s.re : ℂ) ∅
    (fun _ => 1) (by simp)
  obtain ⟨hφ₀, hφ₀c, -⟩ := hsph
  have hσ : (1 : ℝ) / 2 < ((s.re : ℂ)).re := by simpa using hs
  have hint := AutomorphicForm.weylIntertwiningIntegrand_integrable_of_re_gt_half F hα 1 1 h1 h1 (s.re : ℂ) hσ _
    hφ₀ hφ₀c 1
  have hH : Integrable (fun x : AdeleRing (𝓞 F) F =>
      adelicHeight F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x) ^ p) (adelicAddHaar (𝓞 F) F) := by
    refine hint.norm.congr (ae_of_all _ fun x => ?_)
    simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, if_true, mul_one]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (adelicHeight_pos _), hp]
    simp

  haveI := AutomorphicForm.ContM.firstCountableTopology_adelicGL2 F
  rw [continuous_iff_continuousAt]
  intro g₀
  obtain ⟨C, hCc, hCg₀⟩ := exists_compact_mem_nhds g₀
  obtain ⟨κ, K, hκ, hK⟩ :=
    NumberField.AdelicHeight.exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact F C hCc
  have hK0 : 0 ≤ K := by
    have h := (hK 1 g₀ (mem_of_mem_nhds hCg₀)).2
    rw [one_mul] at h
    have := adelicHeight_pos (F := F) g₀
    have h1' := adelicHeight_pos (F := F) (1 : AdelicGL2 (𝓞 F) F)
    nlinarith
  show ContinuousAt (fun g => ∫ x, φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * g) ∂(adelicAddHaar (𝓞 F) F)) g₀
  refine MeasureTheory.continuousAt_of_dominated
    (bound := fun x => max Cφ 0 * (K ^ p * adelicHeight F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x) ^ p))
    ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun g =>
      (AutomorphicForm.weylIntertwiningIntegrand_integrable_of_re_gt_half F hα μ ν hμ hν s hs φ hφ hφc
        g).aestronglyMeasurable
  · filter_upwards [hCg₀] with g hg
    refine ae_of_all _ fun x => ?_
    have hle := (hK ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x) g hg).2
    have hHx := (adelicHeight_pos (F := F) ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x)).le
    calc ‖φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * g)‖
        ≤ Cφ * adelicHeight F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * g) ^ p := by rw [hp]; exact hCφ _
      _ ≤ max Cφ 0 * adelicHeight F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * g) ^ p :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (adelicHeight_pos _).le _)
      _ ≤ max Cφ 0 * (K * adelicHeight F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x)) ^ p :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (adelicHeight_pos _).le hle hp0) (le_max_right _ _)
      _ = max Cφ 0 * (K ^ p * adelicHeight F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x) ^ p) := by
          rw [Real.mul_rpow hK0 hHx]
  · exact (hH.const_mul _).const_mul _
  · exact ae_of_all _ fun x => (hφc.comp (continuous_const.mul continuous_id)).continuousAt

end S_AutomorphicForm_continuous_weylIntertwiningIntegral_of_re_gt_half
end P2MW
export P2MW.S_AutomorphicForm_continuous_weylIntertwiningIntegral_of_re_gt_half (solution)
