-- Prove2me | Definitions.Def_MarkovProcess_Semigroup_Basic_SourceClosedV3
-- name    : MarkovProcess_Semigroup_Basic_SourceClosedV3
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-28T12:37:48.178384+00:00
-- url     : https://prove2.me/theorems/602f08a9-cdf8-47bf-a331-622a531dc3d1
-- title:
--   MarkovProcess definitions: Semigroup.Basic
-- statement:
--   Scott Armstrong’s MarkovProcess library, module `MarkovProcess.Semigroup.Basic`. This source-preserving bundle supplies the non-theorem declarations and definition-embedded lemmas used in the main Markov process formalisation.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Semigroup/Basic.lean#L1-L103

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



variable (S : StronglyContinuousContractionSemigroup E)

























end StronglyContinuousContractionSemigroup

end MarkovProcess.Semigroup


