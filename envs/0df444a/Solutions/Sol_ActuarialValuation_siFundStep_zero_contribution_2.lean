-- Prove2me | solution 2 for ActuarialValuation.siFundStep_zero_contribution
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:42.335545+00:00
-- url     : https://prove2.me/submissions/a8b726a5-8357-4896-9cae-160d47623c0a

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siFundStep

open ActuarialValuation

theorem solution (fund gross : ℝ) : siFundStep fund 0 gross=fund*gross := by simp [siFundStep]

