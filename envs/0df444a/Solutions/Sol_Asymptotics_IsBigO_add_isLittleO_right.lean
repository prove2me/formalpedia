-- Prove2me | solution 1 for Asymptotics.IsBigO.add_isLittleO_right
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:26:24.26991+00:00
-- url     : https://prove2.me/submissions/278c62f6-4fae-4bb0-a0c5-ce4d73402b91

import Mathlib.Analysis.Asymptotics.Lemmas

open Filter Asymptotics

theorem solution {f g : ℝ → ℝ} (h : g =o[atTop] f) :
    f =O[atTop] (f + g) := by
  exact h.right_isBigO_add'
