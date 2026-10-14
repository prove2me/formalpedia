-- Prove2me | solution 1 for ActuarialValuation.ipPoi_summable
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T12:12:53.51229+00:00
-- url     : https://prove2.me/submissions/a15282c7-f263-4a33-bd4e-0cf1d43ec3ae

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ipPoisson
open ActuarialValuation

theorem solution(l : ℝ) : Summable (ipPoisson l) := by
  unfold ipPoisson
  have h := Real.summable_pow_div_factorial l
  simpa [mul_div_assoc] using h.mul_left (Real.exp (-l))
