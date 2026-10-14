-- Prove2me | solution 1 for ActuarialValuation.crExpected_const
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:04:06.904309+00:00
-- url     : https://prove2.me/submissions/0201281b-0200-463c-b36c-d54901365ce7

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crExpected

import Mathlib.Tactic.Ring

import Mathlib.Algebra.BigOperators.Ring.Finset

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p : Fin n→ℝ) (c : ℝ) (hn : (∑ i : Fin n,p i)=1) : crExpected p (fun _=>c)=c := by
  unfold crExpected
  calc
    (∑ i : Fin n, p i * c) = (∑ i : Fin n, p i) * c := by
      rw [Finset.sum_mul]
    _ = c := by rw [hn]; ring
