-- Prove2me | solution 1 for ActuarialValuation.bdForwardGross_inverse
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:06:48.248969+00:00
-- url     : https://prove2.me/submissions/03935007-9bce-4b74-a8b3-49fc19f07392

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdForwardGross
import Definitions.Def_actuarial_bdForwardDiscount

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (D : ℕ → ℝ) (s t : ℕ) (hs : D s ≠ 0) (ht : D t ≠ 0) : bdForwardGross D s t * bdForwardDiscount D s t = 1 := by
  unfold bdForwardGross bdForwardDiscount
  field_simp [hs, ht] <;> ring
