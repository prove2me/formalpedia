-- Prove2me | solution 1 for ActuarialValuation.finiteActionBellmanValue_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:02:26.382387+00:00
-- url     : https://prove2.me/submissions/3c2aec8e-3207-48bc-a73d-bf1e3fac0f1d

import Mathlib
import Definitions.Def_actuarial_finiteActionBellmanValue
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (P : S → A → S → ℝ) (reward : S → A → ℝ)
    (v : ℝ) (next : S → ℝ) (s : S) (a : A) :
    reward s a + v * (∑ t : S, P s a t * next t) ≤
      finiteActionBellmanValue P reward v next s := by
  classical
  change (fun b : A => reward s b +
    v * (∑ t : S, P s b t * next t)) a ≤
    (Finset.univ : Finset A).sup' Finset.univ_nonempty
      (fun b : A => reward s b + v * (∑ t : S, P s b t * next t))
  exact Finset.le_sup'
    (fun b : A => reward s b + v * (∑ t : S, P s b t * next t))
    (Finset.mem_univ a)
