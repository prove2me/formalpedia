-- Prove2me | Definitions.Def_MarkovProcess_Semigroup_Basic
-- name    : MarkovProcess_Semigroup_Basic
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T13:12:00.93235+00:00
-- url     : https://prove2.me/theorems/b29218c3-e467-4ca8-95f0-e88ee8326672
-- title:
--   Strongly continuous contraction semigroups on real normed spaces
-- statement:
--   A strongly continuous contraction semigroup consists of a family of real continuous linear operators indexed by nonnegative time. It satisfies the identity law at time zero, the semigroup composition law at additive times, operator norm at most one, and continuity of every orbit. The definition additionally provides function coercion so a semigroup can be applied to a time. This is the basic functional-analytic interface in Scott Armstrong's MarkovProcess library, ported from an Apache-2.0-licensed source.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Semigroup/Basic.lean#L1-L36

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Strongly continuous contraction semigroups

This file provides a small reusable interface for strongly continuous contraction
semigroups on real normed spaces, parametrized by nonnegative real time.
-/

open Filter Topology

namespace MarkovProcess.Semigroup

/-- A strongly continuous contraction semigroup on a real normed space. -/
structure StronglyContinuousContractionSemigroup (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] where
  /-- The continuous linear time-evolution operator. -/
  operator : NNReal → E →L[ℝ] E
  operator_zero : operator 0 = ContinuousLinearMap.id ℝ E
  operator_add : ∀ s t, operator (s + t) = (operator s).comp (operator t)
  opNorm_le_one : ∀ t, ‖operator t‖ ≤ 1
  continuous_orbit : ∀ x, Continuous (fun t ↦ operator t x)

namespace StronglyContinuousContractionSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

instance : CoeFun (StronglyContinuousContractionSemigroup E)
    (fun _ ↦ NNReal → E →L[ℝ] E) where
  coe S := S.operator

end StronglyContinuousContractionSemigroup
end MarkovProcess.Semigroup


