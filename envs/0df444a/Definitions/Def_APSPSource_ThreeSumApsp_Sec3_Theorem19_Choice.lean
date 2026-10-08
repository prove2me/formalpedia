-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Theorem19_Choice
-- name    : APSPSource_ThreeSumApsp_Sec3_Theorem19_Choice
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T07:23:39.497393+00:00
-- url     : https://prove2.me/theorems/31012601-f7f6-4c93-aeb0-40445ddf900f
-- title:
--   Admissible parameter choices for the Exact Triangle cost analysis
-- statement:
--   For natural numbers $n,D$ and real numbers $\eta,c$, a parameter choice packages the conditions
--
--   $$16\le D,\qquad \frac{n^{1/18}}{c}\le D\le n^{1/18},\qquad c>0,\qquad 0\le\eta\le\frac14.$$
--
--   Here $n$ is the input size, $D$ is the intermediate dimension, $c$ measures the allowed loss from rounding that dimension, and $\eta$ controls the later choice $g=\lceil D^\eta\rceil$.
--
--   The predicate records the shared hypotheses for the two parameter regimes in the source's Theorem 19 cost analysis. It neither chooses parameters nor asserts the resulting running-time bound.
--
--   References:
--
--   1. [Source formalization: parameter-choice predicate](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec3/Theorem19/Choice.lean#L36-L50).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec3/Theorem19/Choice.lean#L36-L50

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Log
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# The cost analysis of Theorem 19 for a general choice of the parameters

The two halves of the proof of Theorem 19 are the same computation with different numbers.  Both
apply Theorem 17 with a number `D ≥ 16` between `n^{1/18}/c` and `n^{1/18}` and with `g = ⌈D^η⌉`,
and solve each of the at most `4ng` instances with a saving `D^{2η}`.  Such a pair `D`, `η` is a
`Choice`, and the computation is carried out here for every choice.

1. A choice satisfies the hypotheses `16 ≤ D ≤ n` and `1 ≤ g ≤ √D` of Theorem 17 and the hypothesis
   `D^18 ≤ n` of Corollaries 15 and 16 (`Choice.sixteen_le`, `Choice.le_n`, `Choice.one_le_ceil`,
   `Choice.ceil_le_sqrt`, `Choice.pow_eighteen_le`).
2. The lower bound on `D` gives `D^{-η} ≤ c^η n^{-η/18}` (`Choice.saving`), and the upper bound
   gives `D^a ≤ n^{a/18}` (`Choice.rpow_le_rpow_div`).
3. Each of the four terms of the running time is `O(n^{3-η/18})` up to logarithms: the instances
   (`Choice.instances_le`) and the scans (`Choice.scans_le`) by the first bound, the choice of `p`
   (`Choice.strassen_le`) and building the instances (`Choice.build_le`) by the second.
4. So is their sum (`exists_total_le`).
-/

@[expose] public section

namespace ThreeSumApsp

namespace Theorem19

/-- A choice of the parameters of Theorem 17 as in both halves of the proof of Theorem 19: `D ≥ 16`
lies between `n^{1/18}/c` and `n^{1/18}`, and `g = ⌈D^η⌉` with `0 ≤ η ≤ 1/4`. -/
structure Choice (n D : ℕ) (η c : ℝ) : Prop where
  /-- `D ≥ 16`, as Theorem 17 asks. -/
  sixteen_le : 16 ≤ D
  /-- `D ≤ n^{1/18}`. -/
  le_root : (D : ℝ) ≤ (n : ℝ) ^ (1 / 18 : ℝ)
  /-- `D ≥ n^{1/18}/c`. -/
  root_div_le : (n : ℝ) ^ (1 / 18 : ℝ) / c ≤ (D : ℝ)
  /-- The constant `c` is positive. -/
  c_pos : 0 < c
  /-- `η ≥ 0`. -/
  η_nonneg : 0 ≤ η
  /-- `η ≤ 1/4`, so that `g ≤ √D`. -/
  η_le : η ≤ 1 / 4










namespace Choice

variable {n D : ℕ} {η c : ℝ} (P : Choice n D η c)
include P

/-! ### The hypotheses of Theorem 17 and of Corollaries 15 and 16 -/

















































/-! ### Logarithms -/









/-! ### Powers of `D` in terms of `n` -/



































/-! ### The four terms of the running time

`Λ` is the logarithmic factor of the result, `log² n` or `log n`. -/






































































end Choice










































end Theorem19

end ThreeSumApsp


