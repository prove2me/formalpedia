-- Prove2me | solution 1 for AllocationIndices.Precedence.nonpreemptive_jobs_index_theorem
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T14:51:53.76268+00:00
-- url     : https://prove2.me/submissions/4213078b-a3c8-4957-80a3-49513932a3d3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AllocationIndices_Precedence_eps_fi_star_near_optimal
import Theorems.Thm_AllocationIndices_Precedence_optimal_policy_is_fi_policy
import Theorems.Thm_AllocationIndices_Precedence_fi_policy_is_fi_star_policy

open MeasureTheory
open AllocationIndices.Precedence

theorem solution {n : ℕ} (F : JobFamily n) (A : Finset (Fin n))
    (π : Policy n) :
    (IsFIStarPolicy F A π ↔ IsFIPolicy F A π) ∧
      (IsFIPolicy F A π ↔ IsOptimalPolicy F A π) := by
  -- FI* ⇒ optimal: Corollary 4.17 with ε = 0
  have hStarOpt : IsFIStarPolicy F A π → IsOptimalPolicy F A π := by
    rintro ⟨hfeas, ρ, hρ, hae⟩
    refine ⟨hfeas, fun g hg => ?_⟩
    have hε : IsEpsFIStarPolicy F A 0 π := by
      refine ⟨hfeas, ρ, fun h hh => ?_, hae⟩
      obtain ⟨hf, hr⟩ := hρ h hh
      exact ⟨hf, by rw [hr]; simp⟩
    have := eps_fi_star_near_optimal F A 0 le_rfl π hε g hg
    simpa using this
  have hOptFI := optimal_policy_is_fi_policy F A π
  have hFIStar := fi_policy_is_fi_star_policy F A π
  exact ⟨⟨fun h => hOptFI (hStarOpt h), hFIStar⟩,
    ⟨fun h => hStarOpt (hFIStar h), hOptFI⟩⟩
