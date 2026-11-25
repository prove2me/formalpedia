-- Prove2me | Definitions.Def_SourceProof_8c53727c7bcd2ff9583c7bbd
-- name    : SourceProof_8c53727c7bcd2ff9583c7bbd
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:47:21.173196+00:00
-- url     : https://prove2.me/theorems/d027d748-c7d3-4698-8484-47ad5d6b952e
-- title:
--   StochLean source theorem: ProbabilityTheory.exists_positive_predictableStoppingTime_disjoint_graph_restrictions

import Definitions.Def_SourceProof_0a28bfe8bb403463b49115a5
import Definitions.Def_SourceProof_76f262a7dcf49af74032efc9
import Definitions.Def_SourceProof_7a200839927b2232bfb83618
import Definitions.Def_SourceProof_a460d17c7805098bd6a011a6
import Definitions.Def_SourceProof_bd5db35608e4f06856d6b838
import Definitions.Def_SourceProof_d6d3239f29afcc05f08f5261
import Definitions.Def_SourceProof_f73bbc630aabc3c5fda26318

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Disjoint finite graphs for a sequence of predictable times

Restrict each predictable time to the event that no earlier index represents
the same finite lifetime. The comparison events are measurable strictly before
that time, so the existing predictable-restriction theorem applies. The least
index realizing a finite graph point preserves it exactly, including time zero.
The restricted finite graphs are pairwise disjoint on every path.

A positive-time version further restricts to the positive-lifetime event.
Its times are strictly positive everywhere (infinity is allowed), and their
graphs cover precisely the positive part of the original graph union. This
separates positive jumps from the source initial-jump convention.

All graph statements use the existing finite `stoppingTimeGraph` owner.
No graph point or process value at infinity is introduced.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ}


theorem _root_.Prove2MeSourceProof.h_8c53727c7bcd2ff9583c7bbd
    (σ : ℕ → Ω → WithTop ℝ≥0) (hσ : ∀ n, IsPredictableStoppingTime F (σ n) P)
    (hF : F.IsUsual P) :
    ∃ η : ℕ → Ω → WithTop ℝ≥0,
      (∀ n, IsPredictableStoppingTime F (η n) P) ∧
        (∀ n ω, 0 < η n ω) ∧
          (∀ n, stoppingTimeGraph (η n) ⊆ stoppingTimeGraph (σ n)) ∧
            Pairwise (fun n m ↦ Disjoint (stoppingTimeGraph (η n)) (stoppingTimeGraph (η m))) ∧
              (⋃ n, stoppingTimeGraph (η n)) =
                (Ioi 0 ×ˢ univ) ∩ ⋃ n, stoppingTimeGraph (σ n) := by
  classical
  obtain ⟨ρ, hρ, hsub, hd, hu⟩ :=
    _root_.Prove2MeSourceProof.h_a460d17c7805098bd6a011a6 σ hσ hF
  let η (n : ℕ) := ProbabilityTheory.restrictedStoppingTime (ρ n) {ω | 0 < ρ n ω}
  have hη (n : ℕ) : ProbabilityTheory.IsPredictableStoppingTime F (η n) P :=
    (_root_.Prove2MeSourceProof.h_bd5db35608e4f06856d6b838 (hρ n)) hF
      ((_root_.Prove2MeSourceProof.h_d6d3239f29afcc05f08f5261 (hρ n).1) measurableSet_Ioi)
  have hηsub (n : ℕ) : ProbabilityTheory.stoppingTimeGraph (η n) ⊆ ProbabilityTheory.stoppingTimeGraph (ρ n) := by
    rw [show ProbabilityTheory.stoppingTimeGraph (η n) =
      ProbabilityTheory.stoppingTimeGraph (ρ n) ∩ (univ ×ˢ {ω | 0 < ρ n ω}) from
        _root_.Prove2MeSourceProof.h_76f262a7dcf49af74032efc9 (ρ n) _]
    exact inter_subset_left
  have hηg (n : ℕ) : ProbabilityTheory.stoppingTimeGraph (η n) =
      (Ioi 0 ×ˢ univ) ∩ ProbabilityTheory.stoppingTimeGraph (ρ n) := by
    rw [show ProbabilityTheory.stoppingTimeGraph (η n) =
      ProbabilityTheory.stoppingTimeGraph (ρ n) ∩ (univ ×ˢ {ω | 0 < ρ n ω}) from
        _root_.Prove2MeSourceProof.h_76f262a7dcf49af74032efc9 (ρ n) _]
    ext p
    simp only [mem_inter_iff, mem_prod, mem_univ, true_and, and_true,
      mem_Ioi, mem_ofPred_eq, _root_.Prove2MeSourceProof.h_f73bbc630aabc3c5fda26318]
    constructor
    · rintro ⟨he, hp⟩
      rw [he] at hp
      exact ⟨WithTop.coe_lt_coe.mp hp, he⟩
    · rintro ⟨hp, he⟩
      refine ⟨he, ?_⟩
      rw [he]
      exact WithTop.coe_lt_coe.mpr hp
  refine ⟨η, hη, ?_, fun n ↦ (hηsub n).trans (hsub n), ?_, ?_⟩
  · intro n ω
    change 0 < ProbabilityTheory.restrictedStoppingTime (ρ n) {ω | 0 < ρ n ω} ω
    by_cases hp : 0 < ρ n ω
    · rw [_root_.Prove2MeSourceProof.h_0a28bfe8bb403463b49115a5 (ρ n) hp]
      exact hp
    · rw [_root_.Prove2MeSourceProof.h_7a200839927b2232bfb83618 (ρ n) hp]
      exact WithTop.coe_lt_top 0
  · intro n m hnm
    exact (hd hnm).mono (hηsub n) (hηsub m)
  · calc
      _ = ⋃ n, (Ioi 0 ×ˢ univ) ∩ ProbabilityTheory.stoppingTimeGraph (ρ n) := iUnion_congr hηg
      _ = (Ioi 0 ×ˢ univ) ∩ ⋃ n, ProbabilityTheory.stoppingTimeGraph (ρ n) := by rw [inter_iUnion]
      _ = _ := by rw [hu]
end ProbabilityTheory


