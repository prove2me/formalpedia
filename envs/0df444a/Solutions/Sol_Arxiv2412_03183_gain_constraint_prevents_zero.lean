-- Prove2me | solution 1 for Arxiv2412_03183.gain_constraint_prevents_zero
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T19:47:37.222038+00:00
-- url     : https://prove2.me/submissions/308734ad-603e-4058-8cc2-548e430ab6bd

import Mathlib
import Definitions.Def_Arxiv2412_03183_Basic

open Arxiv2412_03183 in
theorem solution {S : Type*} {N : S → ℕ} (g : Gains N)
    (hg : g ∈ gainFeasible N) (α : S) (hα : 0 < N α) :
    ∃ i : Fin (N α), 1 ≤ ‖g ⟨α, i⟩‖ := by
  by_contra h
  push Not at h
  have hs := hg α
  have hne : (Finset.univ : Finset (Fin (N α))).Nonempty := Finset.univ_nonempty_iff.mpr ⟨⟨0, hα⟩⟩
  have := Finset.sum_lt_sum_of_nonempty hne (fun i _ => h i)
  simp at this
  linarith
