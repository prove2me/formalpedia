-- Prove2me | solution 1 for ActuarialValuation.finiteStageBellmanMaximum_attained
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:00:34.397578+00:00
-- url     : https://prove2.me/submissions/3629bc63-18ee-407d-b424-c5238f06c026

import Mathlib
import Definitions.Def_actuarial_finiteStageActionReturn
import Definitions.Def_actuarial_finiteStageBellmanMaximum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] (P : S → A → S → ℝ) (reward : S → A → ℝ)
  (v : ℝ) (next : S → ℝ) (s : S)
  :
  ∃ a : A, finiteStageBellmanMaximum P reward v next s =
  finiteStageActionReturn P reward v next s a := by
  show ∃ a : A, Finset.univ.sup' Finset.univ_nonempty
      (fun a => finiteStageActionReturn P reward v next s a) =
    finiteStageActionReturn P reward v next s a
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun a => finiteStageActionReturn P reward v next s a)
  exact ⟨a, ha⟩
