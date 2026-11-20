-- Prove2me | Definitions.Def_SourceProof_a8667ac036da36820cd0dc56
-- name    : SourceProof_a8667ac036da36820cd0dc56
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T19:48:32.171208+00:00
-- url     : https://prove2.me/theorems/32c1bc97-c094-4688-9e3a-50f426dc913e
-- title:
--   LevyStochCalc source module: SourceProof_a8667ac036da36820cd0dc56
-- statement:
--   The original source theorem `ProbabilityTheory.exists_modification_holder_iSup'` comes from the `BrownianMotion.Continuity.KolmogorovChentsov` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_f1692fb100d8a753cf24e001

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
# Kolmogorov-Chentsov theorem

-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology Asymptotics

section aux

end aux

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω}
  {X : T → Ω → E} {c : ℝ≥0∞} {d p q : ℝ} {M β : ℝ≥0} {P : Measure Ω}
  {U : Set T}

section PseudoEMetricSpace

variable [PseudoEMetricSpace T] [PseudoEMetricSpace E]

section HolderSet

end HolderSet

variable [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [hE : Nonempty E]
  [SecondCountableTopology T]

variable [IsFiniteMeasure P]

theorem _root_.Prove2MeSourceProof.h_a8667ac036da36820cd0dc56 {C : ℕ → Set T} {c : ℕ → ℝ≥0∞} {p q : ℕ → ℝ} {M : ℕ → ℝ≥0}
    (hC : IsCoverWithBoundedCoveringNumber C (Set.univ : Set T) c (fun _ ↦ d))
    (hX : ∀ n, IsKolmogorovProcess X P (p n) (q n) (M n)) (hc : ∀ n, c n ≠ ∞)
    (hd_pos : 0 < d) (hdq_lt : ∀ n, d < q n) :
    ∃ Y : T → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ t, Y t =ᵐ[P] X t)
      ∧ ∀ ω t (β : ℝ≥0) (_ : 0 < β) (_ : β < ⨆ n, (q n - d) / (p n)),
        ∃ U ∈ 𝓝 t, ∃ C, HolderOnWith C β (Y · ω) U := by
  have hp_pos : ∀ n, 0 < p n := fun n ↦ (hX n).p_pos
  by_cases h_bdd : BddAbove (Set.range fun n ↦ (q n - d) / p n)
  swap
  · refine ⟨X, (hX 0).measurable, fun _ ↦ EventuallyEq.rfl, fun ω t β hβ_pos hβ_lt ↦ ?_⟩
    simp only [ciSup_of_not_bddAbove h_bdd, Real.sSup_empty] at hβ_lt
    norm_cast at hβ_lt
    exact absurd hβ_pos hβ_lt.not_gt
  have h_ratio_pos n : 0 < (q n - d) / p n := by
    have : 0 < q n - d := by bound
    specialize hp_pos n
    positivity
  let β : ℕ → ℝ≥0 := fun n ↦ ⟨(q n - d) / p n, (h_ratio_pos n).le⟩
  have hβ_pos : ∀ n, 0 < β n := fun n ↦ mod_cast h_ratio_pos n
  have h_exists := fun n ↦ _root_.Prove2MeSourceProof.h_f1692fb100d8a753cf24e001 hC (hX n) hc hd_pos (hdq_lt n)
  choose Z hZ_meas hZ_ae_eq hZ_holder hZ_limit using h_exists
  have hZ_cont n ω : Continuous fun t ↦ Z n t ω := by
    refine continuous_iff_continuousAt.mpr fun t ↦ ?_
    obtain ⟨U, hU_mem, hU⟩ := hZ_holder n ω t
    have hβ_pos_half : 0 < β n / 2 := by specialize hβ_pos n; positivity
    specialize hU (β n / 2) hβ_pos_half ?_
    · exact half_lt_self (h_ratio_pos _)
    · obtain ⟨_, h⟩ := hU
      exact (h.continuousOn hβ_pos_half).continuousAt hU_mem
  have hZ_ae_eq' n : ∀ᵐ ω ∂P, ∀ t, edist (Z n t ω) (Z 0 t ω) = 0 := by
    refine ProbabilityTheory.indistinguishable_of_edist_modification (ae_of_all _ (hZ_cont n))
      (ae_of_all _ (hZ_cont 0)) fun t ↦ ?_
    filter_upwards [hZ_ae_eq n t, hZ_ae_eq 0 t] with ω hω₁ hω₂
    simp [hω₁, hω₂]
  rw [← ae_all_iff] at hZ_ae_eq'
  let A := {ω | ∀ n t, edist (Z n t ω) (Z 0 t ω) = 0}
  have hA : MeasurableSet A := by
    have : A = ⋂ n, {ω | ∀ t, edist (Z n t ω) (Z 0 t ω) = 0} := by ext; simp [A]
    rw [this]
    refine MeasurableSet.iInter (fun n ↦ ?_)
    refine Measurable.measurableSet_edist_eq_zero_of_continuous (hZ_cont n) (hZ_cont 0) fun t ↦ ?_
    refine ProbabilityTheory.IsLimitOfIndicator.measurable_edist (hX n).measurable (hX 0).measurable
      (hX 0).measurablePair (hZ_limit n) (hZ_limit 0) t t
  have hA_ae : ∀ᵐ ω ∂P, ω ∈ A := hZ_ae_eq'
  classical
  let Y (t : T) (ω : Ω) : E := if ω ∈ A then Z 0 t ω else Nonempty.some inferInstance
  refine ⟨Y, fun t ↦ Measurable.ite hA (hZ_meas 0 t) (by fun_prop), fun t ↦ ?_, ?_⟩
  · filter_upwards [hA_ae, hZ_ae_eq 0 t] with ω hω hω₂
    simpa only [hω, ↓reduceIte, Y] using hω₂
  · intro ω t β₀ hβ₀_pos hβ₀_lt
    by_cases hω : ω ∈ A
    swap; · exact ⟨.univ, by simp [hω, Y, HolderOnWith]⟩
    simp only [hω, ↓reduceIte, Y]
    obtain ⟨n, hn⟩ : ∃ n, β₀ < β n := by
      rwa [lt_ciSup_iff h_bdd] at hβ₀_lt
    refine ⟨(hZ_holder n ω t).choose, (hZ_holder n ω t).choose_spec.1, ?_⟩
    obtain ⟨C, hC⟩ := (hZ_holder n ω t).choose_spec.2 β₀ hβ₀_pos hn
    refine ⟨C, ?_⟩
    refine hC.congr_edist fun s t hs ht ↦ ?_
    rw [edist_congr_right (hω n s), edist_congr_left (hω n t)]
end PseudoEMetricSpace

section EMetricSpace

variable [PseudoEMetricSpace T] [EMetricSpace E] [hE : Nonempty E]

variable [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [SecondCountableTopology T]

variable [IsFiniteMeasure P]

end EMetricSpace

end ProbabilityTheory


