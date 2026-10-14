-- Prove2me | solution 1 for ActuarialValuation.pvCdf_above_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:58:37.695582+00:00
-- url     : https://prove2.me/submissions/cba4cc66-d75f-4209-a738-51b0d50eac82

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvCdf

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p loss : Fin n → ℝ) (z : ℝ) (hs : (∑ i : Fin n, p i) = 1) (hmax : ∀ i, loss i ≤ z) : pvCdf p loss z = 1 := by
  unfold pvCdf
  simpa [hmax] using hs
