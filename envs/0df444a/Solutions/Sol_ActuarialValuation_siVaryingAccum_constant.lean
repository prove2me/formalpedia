-- Prove2me | solution 1 for ActuarialValuation.siVaryingAccum_constant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:58:56.489069+00:00
-- url     : https://prove2.me/submissions/d960e3cf-bf22-4112-bcc5-e38502d8d3de

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siFixedAccum
import Definitions.Def_actuarial_siVaryingAccum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (i : ℝ) (n : ℕ) : siVaryingAccum (fun _ => i) n=siFixedAccum i n := by
  simp [siVaryingAccum, siFixedAccum, Finset.prod_const, Finset.card_range]
