-- Prove2me | Definitions.Def_SourceProof_f1692fb100d8a753cf24e001
-- name    : SourceProof_f1692fb100d8a753cf24e001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T19:37:27.752581+00:00
-- url     : https://prove2.me/theorems/9ccb427d-092d-4507-a1a4-3ad6e2f715b7
-- title:
--   LevyStochCalc source module: SourceProof_f1692fb100d8a753cf24e001
-- statement:
--   The original source theorem `ProbabilityTheory.exists_modification_holder'''` comes from the `BrownianMotion.Continuity.KolmogorovChentsov` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_ceb6b5e378b6876adb54ceee

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

theorem _root_.Prove2MeSourceProof.h_f1692fb100d8a753cf24e001 {C : ℕ → Set T} {c : ℕ → ℝ≥0∞}
    (hC : IsCoverWithBoundedCoveringNumber C (Set.univ : Set T) c (fun _ ↦ d))
    (hX : IsKolmogorovProcess X P p q M) (hc : ∀ n, c n ≠ ∞)
    (hd_pos : 0 < d) (hdq_lt : d < q) :
    ∃ Y : T → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ t, Y t =ᵐ[P] X t) ∧
      (∀ ω t, ∃ U ∈ 𝓝 t, ∀ (β : ℝ≥0), 0 < β → β < (q - d) / p → ∃ C, HolderOnWith C β (Y · ω) U) ∧
      IsLimitOfIndicator Y X P Set.univ := by
  have hp_pos : 0 < p := hX.p_pos
  have h_div_pos : 0 < (q - d) / p := by bound
  let ⟨β₀', hβ₀_pos', hβ₀_lt'⟩ := exists_between h_div_pos
  let β₀ : ℝ≥0 := ⟨β₀', hβ₀_pos'.le⟩
  have hβ₀_pos : 0 < β₀ := mod_cast hβ₀_pos'
  have hβ₀_lt : β₀ < (q - d) / p := mod_cast hβ₀_lt'
  classical
  choose Z hZ hZ_eq hZ_holder hZ_extend
    using fun n ↦ _root_.Prove2MeSourceProof.h_ceb6b5e378b6876adb54ceee (hC.hasBoundedCoveringNumber n) (hC.isOpen n) hX
      (hc n) hd_pos hdq_lt
  have hZ_ae_eq : ∀ᵐ ω ∂P, ∀ n t (ht : t ∈ C n), edist (Z n t ω) (Z (n + 1) t ω) = 0 := by
    rw [ae_all_iff]
    intro n
    refine ProbabilityTheory.indistinguishable_of_edist_modification_on (hC.isOpen n)
      (ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun ω ↦ ?_) ?_
    · obtain ⟨_, h⟩ := hZ_holder n β₀ hβ₀_pos hβ₀_lt ω
      exact h.continuousOn hβ₀_pos
    · obtain ⟨_, h⟩ := hZ_holder (n + 1) β₀ hβ₀_pos hβ₀_lt ω
      have h_n_add_one := h.continuousOn hβ₀_pos
      refine h_n_add_one.mono ?_
      exact hC.mono _ _ (Nat.le_succ _)
    · intro t htCn
      filter_upwards [hZ_eq n t htCn, hZ_eq (n + 1) t (hC.mono _ _ (Nat.le_succ _) htCn)]
        with ω hω₁ hω₂
      simp [hω₁, hω₂]
  let A := {ω | ∀ n t (ht : t ∈ C n), edist (Z n t ω) (Z (n + 1) t ω) = 0}
  have hA_eq_le {ω} (hω : ω ∈ A) {n m} (hnm : n ≤ m) (t : C n) : edist (Z n t ω) (Z m t ω) = 0 := by
    induction m with
    | zero => simp only [nonpos_iff_eq_zero] at hnm; subst hnm; simp
    | succ m hm =>
      by_cases hnm' : n ≤ m
      · specialize hm hnm'
        rw [edist_congr_right hm]
        exact hω m t (hC.mono _ _ hnm' t.2)
      · have : n = m + 1 := by omega
        simp [this]
  have hA : MeasurableSet A := by
    have : A = ⋂ n, {ω | ∀ t ∈ C n, edist (Z n t ω) (Z (n + 1) t ω) = 0} := by ext; simp [A]
    rw [this]
    refine MeasurableSet.iInter (fun n ↦ ?_)
    refine _root_.Prove2MeSourceProof.h_440795d18e40286a66795f61 (hC.isOpen n)
      (fun ω ↦ ?_) (fun ω ↦ ?_) fun t ↦ ?_
    · obtain ⟨_, h⟩ :=  hZ_holder n β₀ hβ₀_pos hβ₀_lt ω
      exact h.continuousOn hβ₀_pos
    · obtain ⟨_, h⟩ :=  hZ_holder (n + 1) β₀ hβ₀_pos hβ₀_lt ω
      have h_cont := h.continuousOn hβ₀_pos
      refine h_cont.mono ?_
      exact hC.mono _ _ (Nat.le_succ _)
    · refine ProbabilityTheory.IsLimitOfIndicator.measurable_edist ?_ ?_ ?_ (hZ_extend n) (hZ_extend (n + 1)) _ _
      · exact hX.measurable
      · exact hX.measurable
      · intro i j
        exact hX.measurablePair i j
  have hA_ae : ∀ᵐ ω ∂P, ω ∈ A := hZ_ae_eq
  classical
  -- for each `t`, find `n` such that `t ∈ C n` and call it `nt t`
  have h_mem t : ∃ n, t ∈ C n := by
    have ht : t ∈ ⋃ n, C n := hC.subset_iUnion (by simp : t ∈ Set.univ)
    simpa using ht
  let nt t := Nat.find (h_mem t)
  have hnt t : t ∈ C (nt t) := Nat.find_spec (h_mem t)
  choose A' hA'_meas hA'_ae hZ_tendsto hZC_eq hZCc_eq using hZ_extend
  let Y (t : T) (ω : Ω) : E := if ω ∈ (A ∩ ⋂ n, A' n) then Z (nt t) t ω else hE.some
  have hY_eq {ω} (hω : ω ∈ A ∩ ⋂ n, A' n) n (t : T) (ht : t ∈ C n) :
      edist (Y t ω) (Z n t ω) = 0 := by
    simp only [hω, ↓reduceIte, Y]
    exact hA_eq_le hω.1 (Nat.find_le ht) ⟨t, hnt t⟩
  have hA_inter_meas : MeasurableSet (A ∩ ⋂ n, A' n) :=
    MeasurableSet.inter hA (MeasurableSet.iInter hA'_meas)
  have hA_inter_ae : ∀ᵐ ω ∂P, ω ∈ A ∩ ⋂ n, A' n := by
    simp only [Set.mem_inter_iff, Set.mem_iInter, eventually_and, ae_all_iff]
    exact ⟨hA_ae, hA'_ae⟩
  refine ⟨Y, fun t ↦ Measurable.ite hA_inter_meas (hZ _ _) (by fun_prop), fun t ↦ ?_, ?_, ?_⟩
  · specialize hZ (nt t) t
    filter_upwards [hA_inter_ae, hZ_eq (nt t) t (hnt t)] with ω hω hω₂
    simp only [hω, ↓reduceIte, hω₂, Y, A]
  · intro ω t
    refine ⟨C (nt t), (hC.isOpen (nt t)).mem_nhds (hnt t), ?_⟩
    intro β₀ hβ₀_pos hβ₀_lt
    by_cases hω : ω ∈ A ∩ ⋂ n, A' n
    swap
    · unfold Y
      simp_rw [if_neg hω]
      simp [HolderOnWith]
    obtain ⟨C', hC'⟩ := hZ_holder (nt t) β₀ hβ₀_pos hβ₀_lt ω
    refine ⟨C', ?_⟩
    intro s hs s' hs'
    simp only
    rw [edist_congr_right (hY_eq hω (nt t) s hs), edist_congr_left (hY_eq hω (nt t) s' hs')]
    exact hC' s hs s' hs'
  · refine ⟨A ∩ ⋂ n, A' n, ?_, ?_, ?_, ?_, ?_⟩
    · exact hA.inter (MeasurableSet.iInter hA'_meas)
    · simp only [Set.mem_inter_iff, Set.mem_iInter, eventually_and, ae_all_iff]
      exact ⟨hA_ae, hA'_ae⟩
    · rintro t - ω hω
      simp only [Set.mem_inter_iff, Set.mem_iInter] at hω
      exact hZ_tendsto (nt t) t (hnt t) ω (hω.2 (nt t))
    · intro t _ ω
      classical
      simp only [ProbabilityTheory.indicatorProcess_apply]
      by_cases hω : ω ∈ A ∩ ⋂ n, A' n
      swap
      · simp only [hω, ↓reduceIte, Y, Dense.extend, IsDenseInducing.extend]
        have : @NeBot { x // x ∈ denseCountable T } (comap Subtype.val (𝓝 t)) := by
          apply IsDenseInducing.comap_nhds_neBot (Dense.isDenseInducing_val dense_denseCountable)
        rw [edist_comm]
        exact edist_limUnder_const
      simp only [hω, ↓reduceIte, Y]
      specialize hZC_eq _ t (hnt t)
      simp only [Set.mem_inter_iff, Set.mem_iInter] at hω
      simp only [ProbabilityTheory.indicatorProcess_apply] at hZC_eq
      convert hZC_eq ω
      rw [if_pos]
      exact hω.2 _
    · simp
end PseudoEMetricSpace

section EMetricSpace

variable [PseudoEMetricSpace T] [EMetricSpace E] [hE : Nonempty E]

variable [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [SecondCountableTopology T]

variable [IsFiniteMeasure P]

end EMetricSpace

end ProbabilityTheory


