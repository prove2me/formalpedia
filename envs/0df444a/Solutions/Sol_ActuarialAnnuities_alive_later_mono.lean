-- Prove2me | solution 1 for ActuarialAnnuities.alive_later_mono
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:50:51.60599+00:00
-- url     : https://prove2.me/submissions/0a2b48b4-70fc-4109-a416-d473ed1a62fe

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bAlive
open ActuarialAnnuities

theorem solution (k t u : ℕ) (htu : t ≤ u) : bAlive k u ≤ bAlive k t := by
  simp only [bAlive]
  grind
