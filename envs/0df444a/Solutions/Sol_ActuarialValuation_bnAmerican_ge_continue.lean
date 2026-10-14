-- Prove2me | solution 1 for ActuarialValuation.bnAmerican_ge_continue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:00:51.555113+00:00
-- url     : https://prove2.me/submissions/02b6476c-8f71-4dee-9a11-99820f36560d

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnAmericanNode

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (exercise continuation : ℝ) : continuation ≤ bnAmericanNode exercise continuation := by
  unfold bnAmericanNode
  exact le_max_right _ _
