-- Prove2me | solution 1 for ActuarialValuation.jlProbability_sum_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:40:33.396167+00:00
-- url     : https://prove2.me/submissions/d2691ab8-4899-41a8-aa38-309421fff0ee

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_jlProbability
open ActuarialValuation

theorem solution(px py : ℝ) : (∑ s : Fin 4, jlProbability px py s)=1 := by
  rw [Fin.sum_univ_four]
  simp only [jlProbability, jlBothAlive, jlOnlyXAlive, jlOnlyYAlive, jlBothDead]
  simp only [Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_two]
  norm_num
  ring
