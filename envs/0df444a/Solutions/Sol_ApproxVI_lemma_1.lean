-- Prove2me | solution 1 for ApproxVI.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:04:14.890255+00:00
-- url     : https://prove2.me/submissions/a6a2ec09-2f5b-4657-84be-e2b831349ec0

import Mathlib
import Definitions.Def_ApproxVI_ballNu

open ApproxVI in
theorem solution {d : ℕ} (ν : Fin d → ℝ) (hν : ∀ i, 0 < ν i) (ε : ℝ) (hε : 0 < ε) :
    Convex ℝ (ApproxVI.ballNu ν ε) ∧ IsCompact (ApproxVI.ballNu ν ε) := by
  have key : ApproxVI.ballNu ν ε = Set.univ.pi (fun i => Set.Icc (-(ε * ν i)) (ε * ν i)) := by
    ext y
    have h1 : ApproxVI.wNorm ν y ≤ ε ↔ ∀ i, |y i| / ν i ≤ ε := by
      unfold ApproxVI.wNorm
      rcases isEmpty_or_nonempty (Fin d) with h | h
      · rw [Real.iSup_of_isEmpty]
        exact ⟨fun _ i => isEmptyElim i, fun _ => hε.le⟩
      · exact ciSup_le_iff (Set.finite_range _).bddAbove
    change ApproxVI.wNorm ν y ≤ ε ↔ _
    rw [h1, Set.mem_univ_pi]
    refine forall_congr' (fun i => ?_)
    rw [div_le_iff₀ (hν i), abs_le, Set.mem_Icc]
  rw [key]
  exact ⟨convex_pi (fun i _ => convex_Icc _ _), isCompact_univ_pi (fun i => isCompact_Icc)⟩
