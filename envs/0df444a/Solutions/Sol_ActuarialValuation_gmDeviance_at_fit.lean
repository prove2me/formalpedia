-- Prove2me | solution 1 for ActuarialValuation.gmDeviance_at_fit
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T15:37:38.597689+00:00
-- url     : https://prove2.me/submissions/22d60e33-f26e-44f3-956d-c2945bef5c5a

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_gmPoissonDeviance
open ActuarialValuation

theorem solution(claims : ℝ) : gmPoissonDeviance claims claims=0 := by
  first
  | (simp [gmPoissonDeviance, gmPoissonLogLike, gmSaturatedLike]; done)
  | (norm_num [gmPoissonDeviance, gmPoissonLogLike, gmSaturatedLike]; done)
  | (unfold gmPoissonDeviance gmPoissonLogLike gmSaturatedLike; positivity)
  | (simp only [gmPoissonDeviance, gmPoissonLogLike, gmSaturatedLike]; positivity)
  | (unfold gmPoissonDeviance gmPoissonLogLike gmSaturatedLike; ring)
  | (unfold gmPoissonDeviance gmPoissonLogLike gmSaturatedLike; simp; done)
  | (unfold gmPoissonDeviance gmPoissonLogLike gmSaturatedLike; norm_num; done)
  | (simp [gmPoissonDeviance, gmPoissonLogLike, gmSaturatedLike]; ring)
  | (unfold gmPoissonDeviance gmPoissonLogLike gmSaturatedLike; split_ifs <;> simp_all <;> linarith)
  | (unfold gmPoissonDeviance gmPoissonLogLike gmSaturatedLike; nlinarith [sq_nonneg 0])
  | (simp_all [gmPoissonDeviance, gmPoissonLogLike, gmSaturatedLike]; done)
  | (unfold gmPoissonDeviance gmPoissonLogLike gmSaturatedLike; simp_all; done)
  | rfl
