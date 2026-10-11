-- Prove2me | solution 1 for ActuarialValuation.ipPoisson_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T07:14:11.983057+00:00
-- url     : https://prove2.me/submissions/c593d26b-5eb0-4dca-aa23-802c35b3446a

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ipPoisson
open ActuarialValuation

theorem solution(l : ℝ) (hl : 0≤l) (n : ℕ) : 0≤ ipPoisson l n := by
  unfold ipPoisson
  positivity
