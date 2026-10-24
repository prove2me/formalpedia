-- Prove2me | solution 1 for AssignmentGame.CoreCorners.optimal_matching_has_dual_potentials
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-20T20:40:59.471877+00:00
-- url     : https://prove2.me/submissions/a0ee7d48-b5b2-461c-b7c8-86ff8dc838f8

import Theorems.Thm_AssignmentGame_CoreCorners_core_nonempty
import Theorems.Thm_AssignmentGame_CoreCorners_core_tight_on_optimal_matching
import Theorems.Thm_AssignmentGame_CoreCorners_core_dual_constraints

open AssignmentGame.CoreCorners

theorem solution {M N : Type*} [Fintype M] [Fintype N]
    [DecidableEq M] [DecidableEq N]
    (a : M → N → ℝ) (ha : ∀ i j, 0 ≤ a i j)
    (P : Finset (M × N)) (hP : IsMatching Finset.univ Finset.univ P)
    (hopt : ∑ p ∈ P, a p.1 p.2 = worth a Finset.univ Finset.univ) :
    ∃ (u : M → ℝ) (v : N → ℝ),
      (∀ i, 0 ≤ u i) ∧ (∀ j, 0 ≤ v j) ∧
      (∀ i j, a i j ≤ u i + v j) ∧
      (∀ p ∈ P, u p.1 + v p.2 = a p.1 p.2) := by
  obtain ⟨⟨u, v⟩, hcore⟩ := core_nonempty a ha
  obtain ⟨hu, hv, hdom⟩ := core_dual_constraints a u v hcore
  have htight :=
    (core_tight_on_optimal_matching a ha P hP hopt u v hcore).1
  exact ⟨u, v, hu, hv, hdom, htight⟩
