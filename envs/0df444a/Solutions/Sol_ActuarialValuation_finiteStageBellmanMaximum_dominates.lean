-- Prove2me | solution 1 for ActuarialValuation.finiteStageBellmanMaximum_dominates
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:53:44.539977+00:00
-- url     : https://prove2.me/submissions/c0b21e9b-480b-4665-9b5b-fd31819d6888

import Mathlib
import Definitions.Def_actuarial_finiteStageActionReturn
import Definitions.Def_actuarial_finiteStageBellmanMaximum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] (P : S → A → S → ℝ) (reward : S → A → ℝ)
  (v : ℝ) (next : S → ℝ) (s : S) (a : A)
  :
  finiteStageActionReturn P reward v next s a ≤
  finiteStageBellmanMaximum P reward v next s := by
  show finiteStageActionReturn P reward v next s a ≤
    Finset.univ.sup' Finset.univ_nonempty
      (fun a => finiteStageActionReturn P reward v next s a)
  exact Finset.le_sup' _ (Finset.mem_univ a)
