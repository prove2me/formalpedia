-- Prove2me | solution 1 for ActuarialValuation.crMixture_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:56:14.613757+00:00
-- url     : https://prove2.me/submissions/7d0db975-1c66-4bad-8b62-1d88222cfabf

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crMixWeights

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p q : Fin n→ℝ) (mix : ℝ) (hl0 : 0≤mix) (hl1 : mix≤1) (hp : ∀ i,0≤p i) (hq : ∀ i,0≤q i) (j : Fin n) : 0≤crMixWeights p q mix j := by
  unfold crMixWeights
  apply add_nonneg
  · exact mul_nonneg hl0 (hp j)
  · exact mul_nonneg (sub_nonneg.mpr hl1) (hq j)
