-- Prove2me | solution 1 for AssignmentGame.CoreCorners.matching_extends_to_equiv
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-20T21:09:05.813946+00:00
-- url     : https://prove2.me/submissions/4c767b58-875b-4eb6-9b3d-01c6ea077d2d

import Definitions.Def_AssignmentGame_CoreCorners_Game

open AssignmentGame.CoreCorners

theorem solution {M N : Type*} [Fintype M] [Fintype N]
    [DecidableEq M] [DecidableEq N]
    (e : M ≃ N) (P : Finset (M × N))
    (hP : IsMatching Finset.univ Finset.univ P) :
    ∃ f : M ≃ N, ∀ p ∈ P, f p.1 = p.2 := by
  classical
  let f : {p : M × N // p ∈ P} → M := fun p => p.1.1
  let g : {p : M × N // p ∈ P} → M := fun p => e.symm p.1.2
  have hf : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    exact hP.2.1 p.1 p.2 q.1 q.2 hpq
  have hg : Function.Injective g := by
    intro p q hpq
    apply Subtype.ext
    exact hP.2.2 p.1 p.2 q.1 q.2 (e.symm.injective hpq)
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  refine ⟨σ.trans e, ?_⟩
  intro p hp
  have h := hσ ⟨p, hp⟩
  simpa [f, g] using congrArg e h
