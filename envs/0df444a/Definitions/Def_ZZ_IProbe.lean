-- Prove2me | Definitions.Def_ZZ_IProbe
-- name    : ZZ_IProbe
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-26T14:11:08.396817+00:00
-- url     : https://prove2.me/theorems/78943bfd-0f37-43d5-8c92-e43f79e19f2b
-- title:
--   p
-- statement:
--   p

import Mathlib

open Complex

example (z : ℂ) (t H : ℝ) :
    ((1 - t) • z + t • ((H : ℝ) * Complex.I)).im = (1 - t) * z.im + t * H := by
  simp [Complex.smul_im, Complex.add_im, Complex.I_im, smul_eq_mul]

example (H : ℝ) : ((H : ℝ) * Complex.I).im = H := by simp


