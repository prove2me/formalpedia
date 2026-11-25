-- Prove2me | Definitions.Def_SourceProof_640bd85f93662d293ed47469
-- name    : SourceProof_640bd85f93662d293ed47469
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:51:58.879216+00:00
-- url     : https://prove2.me/theorems/250a7f39-8919-4cc1-bba6-449c88ea4f42
-- title:
--   StochLean source theorem: ProbabilityTheory.IsAccessibleStoppingTime.exists_disjoint_predictable_coefficient_decomposition

import Definitions.Def_StochLean_Probability_Process_Stopping_Classification_F000
import Definitions.Def_SourceProof_8c53727c7bcd2ff9583c7bbd
import Definitions.Def_SourceProof_90c5865c7cef0dcc41ef4e98
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Martingale.Convergence

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Actual predictable-graph coefficients of an accessible single jump

The defining predictable cover of an accessible stopping time is made positive
and disjoint using the existing graph-restriction theorem. Each coefficient is
the original coefficient multiplied by its actual finite collision indicator.
It is measurable at the corresponding stopped field, not assumed measurable
strictly before that time. The predictable times themselves are not restricted
to these merely stopped-measurable collision events.

Disjoint collision events give an absolutely summable sequence of first moments
and an exact closed-step series identity on one common full-measure event.
Infinite original lifetime contributes zero, even if its coefficient is nonzero.
This module handles accessible times; it does not cover a totally inaccessible
component or construct the compensators of the individual predictable jumps.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {σ : Ω → WithTop ℝ≥0} {D : Ω → ℝ}

namespace IsAccessibleStoppingTime

theorem _root_.Prove2MeSourceProof.h_640bd85f93662d293ed47469
    (hσ : IsAccessibleStoppingTime F σ P) (hF : F.IsUsual P)
    (hpos : ∀ᵐ ω ∂P, 0 < σ ω)
    (hD : StronglyMeasurable[hσ.1.measurableSpace] D) (hiD : Integrable D P) :
    ∃ (Γ : ℕ → Ω → WithTop ℝ≥0) (hΓ : ∀ k, IsPredictableStoppingTime F (Γ k) P),
      (∀ k ω, 0 < Γ k ω) ∧
      Pairwise (fun k l ↦ Disjoint (stoppingTimeGraph (Γ k)) (stoppingTimeGraph (Γ l))) ∧
      (∀ᵐ ω ∂P, σ ω ≠ ⊤ → ∃ k, σ ω = Γ k ω) ∧
      let K : ℕ → Ω → ℝ := fun k ↦ {ω | σ ω = Γ k ω ∧ σ ω ≠ ⊤}.indicator D
      (∀ k, StronglyMeasurable[(hΓ k).1.measurableSpace] (K k)) ∧
      (∀ k, Integrable (K k) P) ∧
      HasSum (fun k ↦ ∫ ω, |K k ω| ∂P) (∫ ω in {ω | σ ω ≠ ⊤}, |D ω| ∂P) ∧
      (∑' k, ∫ ω, |K k ω| ∂P) ≤ (∫ ω, |D ω| ∂P) ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        {u | σ u ≤ (t : WithTop ℝ≥0)}.indicator D ω =
          ∑' k, {u | Γ k u ≤ (t : WithTop ℝ≥0)}.indicator (K k) ω := by
  classical
  obtain ⟨θ, hθ, hcover⟩ := hσ.2
  obtain ⟨Γ, hΓ, hpΓ, _, hdΓ, huΓ⟩ :=
    _root_.Prove2MeSourceProof.h_8c53727c7bcd2ff9583c7bbd θ hθ hF
  have hc : ∀ᵐ ω ∂P, σ ω ≠ ⊤ → ∃ k, σ ω = Γ k ω := by
    filter_upwards [hcover, hpos] with ω hω hp hf
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hf
    obtain ⟨k, hk⟩ := hω hf
    have htp : 0 < t := by
      rw [← ht] at hp
      exact WithTop.coe_lt_coe.mp hp
    have hg : (t, ω) ∈ ⋃ k, ProbabilityTheory.stoppingTimeGraph (Γ k) := by
      rw [huΓ]
      refine ⟨⟨htp, mem_univ ω⟩, mem_iUnion.mpr ⟨k, ?_⟩⟩
      exact hk.symm.trans ht.symm
    obtain ⟨j, hj⟩ := mem_iUnion.mp hg
    have hj' : Γ j ω = (t : WithTop ℝ≥0) := hj
    exact ⟨j, ht.symm.trans hj'.symm⟩
  let E : ℕ → Set Ω := fun k ↦ {ω | σ ω = Γ k ω ∧ σ ω ≠ ⊤}
  let K : ℕ → Ω → ℝ := fun k ↦ (E k).indicator D
  have hmE (k : ℕ) : MeasurableSet (E k) :=
    hσ.1.measurableSpace_le _
      ((hσ.1.measurableSet_eq_stopping_time (hΓ k).1).inter
        (hσ.1.measurable (measurableSet_singleton ⊤)).compl)
  have hdE : Pairwise (fun k l ↦ Disjoint (E k) (E l)) := by
    intro k l hkl
    apply disjoint_left.mpr
    intro ω hk hl
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hk.2
    exact disjoint_left.mp (hdΓ hkl)
      (show (t, ω) ∈ ProbabilityTheory.stoppingTimeGraph (Γ k) from hk.1.symm.trans ht.symm)
      (show (t, ω) ∈ ProbabilityTheory.stoppingTimeGraph (Γ l) from hl.1.symm.trans ht.symm)
  have heUnion : (⋃ k, E k) =ᵐ[P] {ω | σ ω ≠ ⊤} := by
    filter_upwards [hc] with ω hω
    apply propext
    constructor
    · intro h
      obtain ⟨k, hk⟩ := mem_iUnion.mp h
      exact hk.2
    · intro hf
      obtain ⟨k, hk⟩ := hω hf
      exact mem_iUnion.mpr ⟨k, hk, hf⟩
  have hmK (k : ℕ) : StronglyMeasurable[(hΓ k).1.measurableSpace] (K k) :=
    (fun p2mMethodArg0 p2mMethodArg1 => _root_.Prove2MeSourceProof.h_90c5865c7cef0dcc41ef4e98 p2mMethodArg0 p2mMethodArg1 hD) hσ.1 (hΓ k).1
  have hiK (k : ℕ) : Integrable (K k) P := hiD.indicator (hmE k)
  have hterm : (fun k ↦ ∫ ω, |K k ω| ∂P) = fun k ↦ ∫ ω in E k, |D ω| ∂P := by
    funext k
    rw [← integral_indicator (hmE k)]
    apply integral_congr_ae
    exact Eventually.of_forall fun ω ↦ by
      by_cases hω : ω ∈ E k <;> simp [K, hω]
  have hsum : HasSum (fun k ↦ ∫ ω, |K k ω| ∂P)
      (∫ ω in {ω | σ ω ≠ ⊤}, |D ω| ∂P) := by
    rw [hterm, ← setIntegral_congr_set heUnion]
    exact hasSum_integral_iUnion hmE hdE hiD.abs.integrableOn
  refine ⟨Γ, hΓ, hpΓ, hdΓ, hc, hmK, hiK, hsum, ?_, ?_⟩
  · rw [hsum.tsum_eq]
    exact setIntegral_le_integral hiD.abs (Eventually.of_forall fun ω ↦ abs_nonneg (D ω))
  · filter_upwards [hc] with ω hω t
    by_cases hf : σ ω = ⊤
    · have hKzero (k : ℕ) : K k ω = 0 := by
        apply indicator_of_notMem
        exact fun h ↦ h.2 hf
      have hs : (∑' k, {u | Γ k u ≤ (t : WithTop ℝ≥0)}.indicator (K k) ω) = 0 := by
        calc
          _ = ∑' _k : ℕ, (0 : ℝ) := tsum_congr fun k ↦ by
            rw [indicator_apply]
            change (if Γ k ω ≤ (t : WithTop ℝ≥0) then K k ω else 0) = 0
            rw [hKzero k, ite_self]
          _ = 0 := tsum_zero
      rw [hs]
      apply indicator_of_notMem
      simpa only [mem_ofPred_eq, hf] using (WithTop.not_top_le_coe t)
    · obtain ⟨k, hk⟩ := hω hf
      have hek : ω ∈ E k := ⟨hk, hf⟩
      have hother (j : ℕ) (hjk : j ≠ k) : K j ω = 0 := by
        apply indicator_of_notMem
        exact fun hj ↦ disjoint_left.mp (hdE hjk) hj hek
      rw [tsum_eq_single k (fun j hj ↦ by
        rw [indicator_apply]
        change (if Γ j ω ≤ (t : WithTop ℝ≥0) then K j ω else 0) = 0
        rw [hother j hj, ite_self])]
      have hKk : K k ω = D ω := indicator_of_mem hek D
      rw [indicator_apply, indicator_apply]
      change (if σ ω ≤ (t : WithTop ℝ≥0) then D ω else 0) =
        if Γ k ω ≤ (t : WithTop ℝ≥0) then K k ω else 0
      rw [hKk, hk]
end IsAccessibleStoppingTime

end ProbabilityTheory


