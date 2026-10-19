-- Prove2me | solution 1 for AngelDevil.nice_devil_reduction
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-18T13:18:39.36848+00:00
-- url     : https://prove2.me/submissions/9650a163-653b-4113-bb8b-d051cf03f583

import Theorems.Thm_AngelDevil_uniform_confinement
import Theorems.Thm_AngelDevil_confinement_to_nice

theorem solution (p : Nat) (hp : 0 < p) :
    ¬ AngelDevil.AngelWins p → ∃ N, 0 < N ∧ AngelDevil.NiceCanConfine p N := by
  intro h
  obtain ⟨N, hN, D, hD⟩ := AngelDevil.uniform_confinement p hp h
  exact ⟨N, hN, AngelDevil.confinement_to_nice p N D hD⟩
