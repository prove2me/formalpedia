-- Prove2me | solution 1 for ActuarialValuation.clReserve_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:29:28.505696+00:00
-- url     : https://prove2.me/submissions/3e69ac28-96ae-424b-94ec-29dbe5c4b89a

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clReserve
open ActuarialValuation

theorem solution(p f : ℝ) (hp : 0 ≤ p) (hf : 1 ≤ f) : 0 ≤ clReserve p f := by
  unfold clReserve clUltimate
  nlinarith
