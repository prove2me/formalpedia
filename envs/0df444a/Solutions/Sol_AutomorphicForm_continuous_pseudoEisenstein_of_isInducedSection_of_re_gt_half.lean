-- Prove2me | solution 1 for AutomorphicForm.continuous_pseudoEisenstein_of_isInducedSection_of_re_gt_half
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/1c385519-d05b-591c-b4d4-d87672112ce8

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_NumberField_AdelicHeight
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Theorems.Thm_AutomorphicForm_isInducedSection_adelicHeight_cpow
import Theorems.Thm_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half
import Theorems.Thm_NumberField_AdelicHeight_exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Theorems.Thm_AutomorphicForm_exists_forall_norm_le_mul_adelicHeight_rpow_of_isInducedSection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_continuous_pseudoEisenstein_of_isInducedSection_of_re_gt_half
p2m_attr_erase "instance" "instCountableOfNumberField_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHeight AutomorphicForm
open scoped NNReal Topology

noncomputable section

namespace R1SlabCE

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F

theorem main :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (s : ℂ) (_hs : 1 / 2 < s.re) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφc : Continuous φ),
    Continuous (pseudoEisenstein F φ) := by
  intro α hα μ ν hμ hν s hs φ hφ hφc
  set σ : ℝ := s.re with hσ
  obtain ⟨Cφ, hCφ0, hCφ⟩ :=
    AutomorphicForm.exists_forall_norm_le_mul_adelicHeight_rpow_of_isInducedSection F hα μ ν hμ hν
      s φ hφ hφc
  obtain ⟨-, h1u, hsph⟩ := AutomorphicForm.isInducedSection_adelicHeight_cpow F
  set h : AdelicGL2 (𝓞 F) F → ℂ := fun g => ((adelicHeight F g : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2)
    with hh
  have hsphσ : IsInducedSection (𝓞 F) F (etaFst 1 α hα (σ : ℂ)) (etaSnd 1 α hα (σ : ℂ)) h :=
    hsph hα (σ : ℂ)
  have hnorm_h : ∀ g, ‖h g‖ = adelicHeight F g ^ (σ + 1 / 2) := by
    intro g
    simp only [hh]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (adelicHeight_pos g)]
    congr 1
    simp [Complex.add_re]
  have hHc := NumberField.AdelicHeight.continuous_adelicHeight F
  have hh_cont : Continuous h := by
    simp only [hh]
    refine Continuous.cpow ?_ continuous_const ?_
    · exact Complex.continuous_ofReal.comp hHc
    · intro g
      exact Or.inl (by simpa using adelicHeight_pos g)
  have hσ' : 1 / 2 < ((σ : ℂ)).re := by simpa [hσ] using hs

  set wn : F → AdelicGL2 (𝓞 F) F := fun ξ =>
    adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) with hwn

  suffices hbig : Continuous fun g : AdelicGL2 (𝓞 F) F => ∑' ξ : F, φ (wn ξ * g) by
    have : pseudoEisenstein F φ = fun g => φ g + ∑' ξ : F, φ (wn ξ * g) := by
      funext g; rw [pseudoEisenstein_apply]
    rw [this]
    exact hφc.add hbig
  refine continuous_iff_continuousAt.2 fun g₀ => ?_

  obtain ⟨C, hCc, hC1⟩ := exists_compact_mem_nhds (1 : AdelicGL2 (𝓞 F) F)
  obtain ⟨κ, K, hκ, hdist⟩ :=
    NumberField.AdelicHeight.exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact F C hCc
  have hK0 : 0 ≤ K := by
    have := (hdist 1 1 (mem_of_mem_nhds hC1)).2
    rw [one_mul] at this
    have hpos := adelicHeight_pos (F := F) 1
    nlinarith
  set S : Set (AdelicGL2 (𝓞 F) F) := {g | g₀⁻¹ * g ∈ C} with hS
  have hnhds : S ∈ 𝓝 g₀ := by
    have hc : Continuous fun g : AdelicGL2 (𝓞 F) F => g₀⁻¹ * g := continuous_const.mul continuous_id
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hC1)

  set u : F → ℝ := fun ξ => Cφ * K ^ (σ + 1 / 2) * ‖h (wn ξ * g₀)‖ with hu
  have hsum : Summable u := by
    have hs0 : Summable fun ξ : F => ‖h (wn ξ * g₀)‖ :=
      AutomorphicForm.bruhatTransversal_summand_norm_summable_of_re_gt_half F hα 1 1 h1u h1u (σ : ℂ)
        hσ' h hsphσ hh_cont g₀
    exact hs0.mul_left _
  have hcont_on : ContinuousOn (fun g : AdelicGL2 (𝓞 F) F => ∑' ξ : F, φ (wn ξ * g)) S := by
    refine continuousOn_tsum (fun ξ => ?_) hsum ?_
    · exact (hφc.comp (continuous_const.mul continuous_id)).continuousOn
    · intro ξ g hg
      have hy : g = g₀ * (g₀⁻¹ * g) := by group
      have hH : adelicHeight F (wn ξ * g) ≤ K * adelicHeight F (wn ξ * g₀) := by
        have := (hdist (wn ξ * g₀) (g₀⁻¹ * g) hg).2
        rw [hy]
        simpa [mul_assoc] using this
      have hσpos : 0 ≤ σ + 1 / 2 := by linarith
      calc ‖φ (wn ξ * g)‖
          ≤ Cφ * adelicHeight F (wn ξ * g) ^ (σ + 1 / 2) := hCφ _
        _ ≤ Cφ * (K * adelicHeight F (wn ξ * g₀)) ^ (σ + 1 / 2) := by
            gcongr
            exact (adelicHeight_pos _).le
        _ = u ξ := by
            simp only [hu]
            rw [Real.mul_rpow hK0 (adelicHeight_pos _).le, hnorm_h]
            ring
  exact hcont_on.continuousAt hnhds

end R1SlabCE

end

open MeasureTheory NumberField AutomorphicForm
open scoped NNReal

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
    Continuous (pseudoEisenstein F φ) :=
  R1SlabCE.main F

end S_AutomorphicForm_continuous_pseudoEisenstein_of_isInducedSection_of_re_gt_half
end P2MW
export P2MW.S_AutomorphicForm_continuous_pseudoEisenstein_of_isInducedSection_of_re_gt_half (solution)
