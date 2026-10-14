-- Prove2me | solution 1 for ActuarialValuation.pvCdf_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:58:14.445158+00:00
-- url     : https://prove2.me/submissions/30640559-84c1-49b3-8220-0a09605786bb

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvCdf

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p loss : Fin n → ℝ) (z : ℝ) (hp : ∀ i, 0 ≤ p i) : 0 ≤ pvCdf p loss z := by
  unfold pvCdf
  apply Finset.sum_nonneg
  intro i hi
  split_ifs
  · exact hp i
  · exact le_refl _
