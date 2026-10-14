-- Prove2me | solution 1 for ActuarialValuation.gmLogLikeEta_zero_claims
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T14:06:23.16405+00:00
-- url     : https://prove2.me/submissions/28ea4f98-6874-48ba-97fa-c15fda27c1cc

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_gmMean
import Definitions.Def_actuarial_gmLogLikeEta
open ActuarialValuation

theorem solution(exposure eta : ℝ) : gmLogLikeEta 0 exposure eta= -gmMean exposure eta := by
  first
  | (simp [gmMean, gmLogLikeEta, gmPoissonLogLike]; done)
  | (norm_num [gmMean, gmLogLikeEta, gmPoissonLogLike]; done)
  | (unfold gmMean gmLogLikeEta gmPoissonLogLike; positivity)
  | (simp only [gmMean, gmLogLikeEta, gmPoissonLogLike]; positivity)
  | (unfold gmMean gmLogLikeEta gmPoissonLogLike; ring)
  | (unfold gmMean gmLogLikeEta gmPoissonLogLike; simp; done)
  | (unfold gmMean gmLogLikeEta gmPoissonLogLike; norm_num; done)
  | (simp [gmMean, gmLogLikeEta, gmPoissonLogLike]; ring)
  | (unfold gmMean gmLogLikeEta gmPoissonLogLike; split_ifs <;> simp_all <;> linarith)
  | (unfold gmMean gmLogLikeEta gmPoissonLogLike; nlinarith [sq_nonneg 0])
  | (simp_all [gmMean, gmLogLikeEta, gmPoissonLogLike]; done)
  | (unfold gmMean gmLogLikeEta gmPoissonLogLike; simp_all; done)
  | rfl
