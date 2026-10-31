-- Prove2me | Definitions.Def_MarkovProcess_V3H_Continuity_DyadicPathChaining_e74fe8f3
-- name    : MarkovProcess_V3H_Continuity_DyadicPathChaining_e74fe8f3
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:11:53.875393+00:00
-- url     : https://prove2.me/theorems/24f2edb2-d061-4221-ad23-7435519ea086
-- title:
--   MarkovProcess source: MarkovProcess_V3H_Continuity_DyadicPathChaining_e74fe8f3
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.EMetricSpace.Basic

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Dyadic chaining on a bounded interval of nonnegative time

This file is deterministic infrastructure for a quantitative modulus of continuity.  It
subdivides the interval `[0, T]` of nonnegative real time into `2 ^ m` equal parts and records
what uniform control of the adjacent increments of a function `f : ℝ≥0 → E` on all subdivisions
from a base level downwards implies for pairs of subdivision points.

Main results:

* `MarkovProcess.dyadicTime`, the `i`-th point of the level-`m` subdivision of `[0, T]`, with its
  monotonicity, refinement and increment estimates;
* `MarkovProcess.HasDyadicAdjacentBound`, the hypothesis that all adjacent increments of `f` on
  the level-`m` subdivision are at most `e`;
* `MarkovProcess.edist_dyadicTime_le_of_hasDyadicAdjacentBound`, the same-level chaining bound;
* `MarkovProcess.edist_dyadicTime_ancestor_le`, the bound from a fine subdivision point to its
  canonical coarse ancestor by the sum of the intervening bounds;
* `MarkovProcess.edist_dyadicTime_le_of_sub_le`, the two-point chaining bound: subdivision points
  of level `n + r` whose indices differ by at most `2 ^ r` are within `2 * (chain sum) + e n`;
* `MarkovProcess.dyadicIndex` and its approximation lemmas, which locate an arbitrary time of
  `[0, T]` between consecutive subdivision points and compare the indices of two nearby times.

Everything here is a statement about a fixed function of time.  No measure, no probability law,
and no continuity of `f` is used or asserted.
-/

open Filter Topology
open scoped ENNReal NNReal

namespace MarkovProcess

section Subdivision

/-- The `i`-th point of the subdivision of `[0, T]` into `2 ^ m` equal parts. -/
noncomputable def dyadicTime (T : ℝ≥0) (m i : ℕ) : ℝ≥0 := T * i / 2 ^ m



@[simp]
theorem p2m_embedded_a7cc40051dec07a7 (T : ℝ≥0) (m : ℕ) : dyadicTime T m 0 = 0 := by
  simp [dyadicTime]











end Subdivision

section Chaining

variable {E : Type*} [PseudoEMetricSpace E]

/-- Every adjacent increment of `f` on the level-`m` subdivision of `[0, T]` is at most `e`. -/
def HasDyadicAdjacentBound (f : ℝ≥0 → E) (T : ℝ≥0) (m : ℕ) (e : ℝ≥0∞) : Prop :=
  ∀ i < 2 ^ m, edist (f (dyadicTime T m i)) (f (dyadicTime T m (i + 1))) ≤ e









end Chaining

section Approximation

/-- The index of the last level-`m` subdivision point of `[0, T]` at or below `s`. -/
noncomputable def dyadicIndex (T : ℝ≥0) (m : ℕ) (s : ℝ≥0) : ℕ := ⌊(s : ℝ) * 2 ^ m / T⌋₊













end Approximation

end MarkovProcess


