-- Prove2me | Definitions.Def_SourceProof_a460d17c7805098bd6a011a6
-- name    : SourceProof_a460d17c7805098bd6a011a6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:42:29.946278+00:00
-- url     : https://prove2.me/theorems/8c6be405-6ab6-4aff-b3ea-ed8d163a9056
-- title:
--   StochLean source theorem: ProbabilityTheory.exists_predictableStoppingTime_disjoint_graph_restrictions

import Definitions.Def_SourceProof_0a28bfe8bb403463b49115a5
import Definitions.Def_SourceProof_59b26859132e89360b279698
import Definitions.Def_SourceProof_76f262a7dcf49af74032efc9
import Definitions.Def_SourceProof_bd5db35608e4f06856d6b838
import Definitions.Def_SourceProof_cdbeee02395da7ffa366081e
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


theorem _root_.Prove2MeSourceProof.h_a460d17c7805098bd6a011a6
    (σ : ℕ → Ω → WithTop ℝ≥0) (hσ : ∀ n, IsPredictableStoppingTime F (σ n) P)
    (hF : F.IsUsual P) :
    ∃ ρ : ℕ → Ω → WithTop ℝ≥0,
      (∀ n, IsPredictableStoppingTime F (ρ n) P) ∧
        (∀ n, stoppingTimeGraph (ρ n) ⊆ stoppingTimeGraph (σ n)) ∧
          Pairwise (fun n m ↦ Disjoint (stoppingTimeGraph (ρ n)) (stoppingTimeGraph (ρ m))) ∧
            (⋃ n, stoppingTimeGraph (ρ n)) = ⋃ n, stoppingTimeGraph (σ n) := by
  classical
  let E (n : ℕ) : Set Ω := {ω | ∀ k < n, ¬ (σ k ω = σ n ω ∧ σ n ω ≠ ⊤)}
  have hE (n : ℕ) : MeasurableSet[(hσ n).1.measurableSpaceBefore] (E n) := by
    have he : E n = ⋂ k : ℕ, ⋂ _ : k < n, {ω | σ k ω = σ n ω ∧ σ n ω ≠ ⊤}ᶜ := by
      ext ω
      simp only [E, mem_ofPred_eq, mem_iInter, mem_compl_iff]
    rw [he]
    exact MeasurableSet.iInter fun k ↦ MeasurableSet.iInter fun _ ↦
      ((_root_.Prove2MeSourceProof.h_cdbeee02395da7ffa366081e (hσ k)) (hσ n).1 (_root_.Prove2MeSourceProof.h_59b26859132e89360b279698 hF)).compl
  let ρ (n : ℕ) := ProbabilityTheory.restrictedStoppingTime (σ n) (E n)
  have hρ (n : ℕ) : ProbabilityTheory.IsPredictableStoppingTime F (ρ n) P :=
    (_root_.Prove2MeSourceProof.h_bd5db35608e4f06856d6b838 (hσ n)) hF (hE n)
  have hg (n : ℕ) : ProbabilityTheory.stoppingTimeGraph (ρ n) =
      ProbabilityTheory.stoppingTimeGraph (σ n) ∩ (univ ×ˢ E n) :=
    _root_.Prove2MeSourceProof.h_76f262a7dcf49af74032efc9 (σ n) (E n)
  have hsub (n : ℕ) : ProbabilityTheory.stoppingTimeGraph (ρ n) ⊆ ProbabilityTheory.stoppingTimeGraph (σ n) := by
    rw [hg]
    exact inter_subset_left
  have hmem {n : ℕ} {p : ℝ≥0 × Ω} (hp : p ∈ ProbabilityTheory.stoppingTimeGraph (ρ n)) : p.2 ∈ E n := by
    rw [hg] at hp
    exact hp.2.2
  have hnodup {n m : ℕ} (hnm : n < m) {p : ℝ≥0 × Ω}
      (hn : p ∈ ProbabilityTheory.stoppingTimeGraph (ρ n)) (hm : p ∈ ProbabilityTheory.stoppingTimeGraph (ρ m)) : False := by
    have hEω := hmem hm
    have hn' : σ n p.2 = (p.1 : WithTop ℝ≥0) := hsub n hn
    have hm' : σ m p.2 = (p.1 : WithTop ℝ≥0) := hsub m hm
    exact hEω n hnm ⟨hn'.trans hm'.symm,
      fun htop ↦ WithTop.coe_ne_top (hm'.symm.trans htop)⟩
  refine ⟨ρ, hρ, hsub, ?_, ?_⟩
  · intro n m hnm
    apply Set.disjoint_left.mpr
    intro p hn hm
    rcases lt_or_gt_of_ne hnm with h | h
    · exact hnodup h hn hm
    · exact hnodup h hm hn
  · apply subset_antisymm (iUnion_mono hsub)
    intro p hp
    have hex : ∃ n, σ n p.2 = (p.1 : WithTop ℝ≥0) := by
      simpa only [mem_iUnion, _root_.Prove2MeSourceProof.h_f73bbc630aabc3c5fda26318] using hp
    let n := Nat.find hex
    have hn : σ n p.2 = (p.1 : WithTop ℝ≥0) := Nat.find_spec hex
    have hEn : p.2 ∈ E n := by
      intro k hkn hk
      exact Nat.find_min hex hkn (hk.1.trans hn)
    apply mem_iUnion.mpr
    refine ⟨n, ?_⟩
    change ProbabilityTheory.restrictedStoppingTime (σ n) (E n) p.2 = (p.1 : WithTop ℝ≥0)
    rw [_root_.Prove2MeSourceProof.h_0a28bfe8bb403463b49115a5 (σ n) hEn]
    exact hn
end ProbabilityTheory


