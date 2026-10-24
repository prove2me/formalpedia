-- Prove2me | solution 1 for AssignmentGame.CoreCorners.core_dual_constraints
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-20T20:40:25.98028+00:00
-- url     : https://prove2.me/submissions/706c1819-c2c9-47c4-b003-16e9fd9b76e4

import Definitions.Def_AssignmentGame_CoreCorners_Game

open AssignmentGame.CoreCorners

theorem solution {M N : Type*} [Fintype M] [Fintype N]
    [DecidableEq M] [DecidableEq N]
    (a : M → N → ℝ) (u : M → ℝ) (v : N → ℝ)
    (hcore : (u, v) ∈ core a) :
    (∀ i, 0 ≤ u i) ∧ (∀ j, 0 ≤ v j) ∧
      ∀ i j, a i j ≤ u i + v j := by
  classical
  have hworth_nonneg (A : Finset M) (B : Finset N) : 0 ≤ worth a A B := by
    unfold worth
    have he : (∅ : Finset (M × N)) ∈ matchings A B := empty_mem_matchings A B
    have h := Finset.le_sup' (fun P : Finset (M × N) => ∑ p ∈ P, a p.1 p.2) he
    simpa using h
  have hu (i : M) : 0 ≤ u i := by
    have h := hcore.2 ({i} : Finset M) (∅ : Finset N)
    simpa using le_trans (hworth_nonneg {i} ∅) h
  have hv (j : N) : 0 ≤ v j := by
    have h := hcore.2 (∅ : Finset M) ({j} : Finset N)
    simpa using le_trans (hworth_nonneg ∅ {j}) h
  refine ⟨hu, hv, ?_⟩
  intro i j
  have hmatching : IsMatching ({i} : Finset M) ({j} : Finset N) ({(i, j)} : Finset (M × N)) := by
    simp [IsMatching]
  have hmem : ({(i, j)} : Finset (M × N)) ∈
      matchings ({i} : Finset M) ({j} : Finset N) := by
    simp [matchings, hmatching]
  have hvalue : a i j ≤ worth a {i} {j} := by
    unfold worth
    have h := Finset.le_sup' (fun P : Finset (M × N) => ∑ p ∈ P, a p.1 p.2) hmem
    simpa using h
  have hcoal := hcore.2 ({i} : Finset M) ({j} : Finset N)
  simpa using le_trans hvalue hcoal
