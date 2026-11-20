-- Prove2me | Definitions.Def_SourceProof_ceb6b5e378b6876adb54ceee
-- name    : SourceProof_ceb6b5e378b6876adb54ceee
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T19:31:25.658399+00:00
-- url     : https://prove2.me/theorems/6ba2012a-25fa-49d6-b90c-9cf084564d81
-- title:
--   LevyStochCalc source module: SourceProof_ceb6b5e378b6876adb54ceee
-- statement:
--   The original source theorem `ProbabilityTheory.exists_modification_holder''` comes from the `BrownianMotion.Continuity.KolmogorovChentsov` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Continuity_KolmogorovChentsov_F002
import Definitions.Def_SourceProof_440795d18e40286a66795f61

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

theorem _root_.Prove2MeSourceProof.h_ceb6b5e378b6876adb54ceee (hT : HasBoundedCoveringNumber U c d)
    (hU : IsOpen U)
    (hX : IsKolmogorovProcess X P p q M)
    (hc : c ≠ ∞) (hd_pos : 0 < d) (hdq_lt : d < q) :
    ∃ Y : T → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ t ∈ U, Y t =ᵐ[P] X t) ∧
      (∀ (β : ℝ≥0), 0 < β → β < (q - d) / p → ∀ ω, ∃ C, HolderOnWith C β (Y · ω) U) ∧
      IsLimitOfIndicator Y X P U := by
  have h_ratio_pos : 0 < (q - d) / p := by
    have : 0 < p := hX.p_pos
    bound
  obtain ⟨β', hβ'_mono, hβ'_mem, hβ'_tendsto⟩ := exists_seq_strictMono_tendsto' h_ratio_pos
  let β : ℕ → ℝ≥0 := fun n ↦ ⟨β' n, (hβ'_mem n).1.le⟩
  have hβ_pos : ∀ n, 0 < β n := fun n ↦ mod_cast (hβ'_mem n).1
  obtain ⟨T', hT'_countable, hT'_dense⟩ := TopologicalSpace.exists_countable_dense T
  classical
  have := fun n ↦ ProbabilityTheory.exists_modification_holder_aux' hT hU hX hc hd_pos hdq_lt
    (hβ_pos n) (mod_cast (hβ'_mem n).2)
  choose Z hZ_meas hZ_ae_eq hZ_holder hZ_isLimit using this
  have hZ_ae_eq' n : ∀ᵐ ω ∂P, ∀ t ∈ U, edist (Z n t ω) (Z 0 t ω) = 0 := by
    refine ProbabilityTheory.indistinguishable_of_edist_modification_on hU
      (ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun ω ↦ ?_) ?_
    · obtain ⟨_, h⟩ := hZ_holder n ω
      exact h.continuousOn (hβ_pos n)
    · obtain ⟨_, h⟩ := hZ_holder 0 ω
      exact h.continuousOn (hβ_pos 0)
    · intro t htU
      filter_upwards [hZ_ae_eq n t htU, hZ_ae_eq 0 t htU] with ω hω₁ hω₂
      simp [hω₁, hω₂]
  rw [← ae_all_iff] at hZ_ae_eq'
  let A := {ω | ∀ n t, t ∈ U → edist (Z n t ω) (Z 0 t ω) = 0}
  have hA : MeasurableSet A := by
    have : A = ⋂ n, {ω | ∀ t, t ∈ U → edist (Z n t ω) (Z 0 t ω) = 0} := by ext; simp [A]
    rw [this]
    refine MeasurableSet.iInter (fun n ↦ ?_)
    refine _root_.Prove2MeSourceProof.h_440795d18e40286a66795f61 hU (fun ω ↦ ?_) (fun ω ↦ ?_)
      fun t ↦ ?_
    · obtain ⟨_, h⟩ := hZ_holder n ω
      exact h.continuousOn (hβ_pos n)
    · obtain ⟨_, h⟩ := hZ_holder 0 ω
      exact h.continuousOn (hβ_pos 0)
    · refine ProbabilityTheory.IsLimitOfIndicator.measurable_edist hX.measurable hX.measurable
        hX.measurablePair (hZ_isLimit n) (hZ_isLimit 0) t t
  have hA_ae : ∀ᵐ ω ∂P, ω ∈ A := hZ_ae_eq'
  classical
  let Y (t : T) (ω : Ω) : E := ProbabilityTheory.indicatorProcess (Z 0) A t ω
  classical
  refine ⟨Y, fun t ↦ Measurable.ite hA (hZ_meas 0 t) (by fun_prop), fun t htU ↦ ?_, ?_, ?_⟩
  · filter_upwards [hA_ae, hZ_ae_eq 0 t htU] with ω hω hω₂
    simpa only [hω, ↓reduceIte, Y, ProbabilityTheory.indicatorProcess_apply] using hω₂
  · intro β₀ hβ₀_pos hβ₀_lt ω
    by_cases hω : ω ∈ A
    swap; · simp [hω, Y, HolderOnWith]
    simp only [hω, ↓reduceIte, Y, ProbabilityTheory.indicatorProcess_apply]
    obtain ⟨n, hn⟩ : ∃ n, β₀ < β n := by
      obtain ⟨n, hn⟩ : ∃ n, β₀ < β' n := (Tendsto.eventually_const_lt hβ₀_lt hβ'_tendsto).exists
      exact ⟨n, mod_cast hn⟩
    suffices ∃ C, HolderOnWith C (β n) (fun x ↦ Z 0 x ω) U by
      obtain ⟨C, hC⟩ := this
      refine HolderOnWith.mono_right' hC hn.le (C' := (Metric.ediam U).toNNReal) ?_
      have h_diam : Metric.ediam U < ∞ := hT.ediam_lt_top
      rw [ENNReal.coe_toNNReal h_diam.ne]
      exact fun x hx y hy ↦ Metric.edist_le_ediam_of_mem hx hy
    simp only [Set.mem_setOf_eq, A] at hω
    obtain ⟨C, hC⟩ := hZ_holder n ω
    refine ⟨C, fun s hs t ht ↦ ?_⟩
    specialize hC s hs t ht
    simp only
    rw [← edist_congr_left (hω n t ht), ← edist_congr_right (hω n s hs)]
    exact hC
  · exact _root_.Prove2MeSourceProof.h_11bb60daeeb4a4b137b43a03 (hZ_isLimit 0) A hA hA_ae
end PseudoEMetricSpace

section EMetricSpace

variable [PseudoEMetricSpace T] [EMetricSpace E] [hE : Nonempty E]

variable [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [SecondCountableTopology T]

variable [IsFiniteMeasure P]

end EMetricSpace

end ProbabilityTheory


