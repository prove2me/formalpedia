-- Prove2me | solution 1 for AlliancePortfolio.Sharing.eq_9
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T19:50:19.147704+00:00
-- url     : https://prove2.me/submissions/5f689f86-41b7-4833-830d-14d6988489b6

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_ShapleyValue
import Definitions.Def_AlliancePortfolio_Sharing_Model
open AlliancePortfolio.Sharing

theorem solution(V b πF sImp sRB : ℝ) :
    φ V b πF sImp sRB F = V + πF + (1 / 3) * b + (1 / 3) * (sImp - sRB) := by
  simp only [φ, Supermodularity.Cooperative.ShapleyValue, game]
  rw [show (Finset.univ.erase (0:Fin 3)).powerset = {∅, {1}, {2}, {1,2}} from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp [F, Nat.factorial]
  norm_num [Finset.card_insert_of_notMem]
  ring
