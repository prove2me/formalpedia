-- Prove2me | solution 1 for AccelVI.MVC.alpha_eq_one_add_beta
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-15T20:01:12.128267+00:00
-- url     : https://prove2.me/submissions/41732d9a-934d-4f92-9a7b-29d3a8c6d9e0

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_AccelVI_MVC_Setting
open AccelVI.MVC

theorem solution(lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1) :
    alphaMVC lam = 1 + betaMVC lam := by
  unfold alphaMVC betaMVC
  have h : 0 < 1 + Real.sqrt (1 - lam ^ 2) := by positivity
  rw [eq_comm, ← sub_eq_zero]
  field_simp
  ring
