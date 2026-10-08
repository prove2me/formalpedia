-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Parameters
-- name    : APSPSource_ThreeSumApsp_Sec3_Parameters
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T08:09:02.385967+00:00
-- url     : https://prove2.me/theorems/43169e90-d899-4a92-82a8-f972f942ff79
-- title:
--   Uniform time shapes and parameters for triangle reductions
-- statement:
--   Write $\ell(u)=\log(\max\{u,2\})$. For a candidate running-time function $T(s,u)$, the good-time predicate requires both
--
--   $$T(s,u)\ge s^2(1+\ell(u))\quad(s\ge1),\qquad
--   \frac{T(s_1,u)}{s_1}\le\frac{T(s_2,u)}{s_2}\quad(1\le s_1\le s_2).$$
--
--   The first is an explicit input-writing lower bound in this formalization; the second is the monotonicity condition used in the reduction. For real constants $K,\delta$, natural exponent $e$, natural size $s$, and real magnitude parameter $u$, define
--
--   $$T_{K,\delta,e}(s,u)=K s^{3-\delta}(\log s+1)^e(1+\ell(u))^2.$$
--
--   The bundle also names the three additional cost expressions
--
--   $$\frac{\kappa n^3\log n}{g},\qquad M(n)D^{3/2},\qquad n^2Dg,$$
--
--   where $n,D,g$ are natural parameters, $\kappa$ is a real weight exponent, and $M(n)$ is a matrix-multiplication cost function. It includes the function $n^{\log_2 7}$, the total number of chunks over all residue classes, and the real-power parameter choices $D=\lfloor n^{1/18}\rfloor_+$ and $g=\lceil D^{0.0315}\rceil_+$.
--
--   These are predicates and expressions used to state later reduction bounds; no running-time claim is asserted merely by defining them. Real powers and divisions use the formalization's total conventions at zero.
--
--   References:
--
--   1. [Source formalization, lines 34–73](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec3/Parameters.lean#L34-L73).
--   2. [Source formalization, lines 85–89](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec3/Parameters.lean#L85-L89).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec3/Parameters.lean#L34-L73; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec3/Parameters.lean#L85-L89

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Log
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.Floor.Div
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
# The parameters and model running times of Sections 3.1 to 3.4

Numbers and functions that the running-time claims of Section 3 and the programs of Section 3 share.
None of them mentions a claim or a machine.

* `TriangleInstance.totalChunks`, the number of chunks in the proof of Theorem 17, and the three
  terms of the additional time of Theorem 17: `termScans`, `termPrime`, `termBuild`.
* The parameters of the proof of Theorem 19: `paramD₅`, `paramG₅` on the route through
  Theorem 5 and `paramD₂₆`, `paramG₂₆` on the route through Corollary 26; `strassen`, the number of
  ring operations of Strassen's algorithm.
* `splitCap`, the size of the pieces into which Corollary 15 splits the query pairs.
* `DivNondecreasing` and `GoodTime`, the condition of Theorem 21(b) on a running time, and
  `uniformTime`, the running time of Theorem 19 as a function of the size and of the bound on the
  weights.  (The number of vertices `n^{1/3}` of Theorem 21(b) is `cbrtCeil n`.)
-/

@[expose] public section

namespace ThreeSumApsp

/-- Proof of Theorem 17: the number of chunks "in all", summed over the residues `ϱ`. -/
noncomputable def TriangleInstance.totalChunks {n : ℕ} (T : TriangleInstance ℤ n) (D p : ℕ) : ℕ :=
  ∑ ϱ : Fin p, numChunks (T.residueClass p ϱ) (queryCap n D)

/-- Theorem 21(b): "with T(s)/s nondecreasing". -/
def DivNondecreasing (T : ℕ → ℝ) : Prop :=
  ∀ s₁ s₂ : ℕ, 1 ≤ s₁ → s₁ ≤ s₂ → T s₁ / s₁ ≤ T s₂ / s₂

/-- Theorem 21(b): a running time "T(s) with T(s)/s nondecreasing", for every fixed bound
`u` on the numbers.

NOTE.  We also ask that `T(s) ≥ s² (1 + log u)`, which is an upper bound for the time to write down
the `3s²` weights of an instance. The paper does not say this, but its bound
`O(n² T(n^{1/3}) log² U)` leaves no room for writing down the instances otherwise.  The condition is
a hypothesis on the running times that are fed into Theorem 21(b), so it makes the claims that use
it weaker, not stronger. -/
def GoodTime (T : ℕ → ℝ → ℝ) : Prop :=
  (∀ (s : ℕ) (u : ℝ), 1 ≤ s → (s : ℝ) ^ 2 * (1 + logU u) ≤ T s u) ∧
    ∀ u : ℝ, DivNondecreasing fun s => T s u

/-- The running time `K s^{3−δ} (log s + 1)^e (1 + log u)²` for Exact Triangle on `s` vertices per
part with weights of absolute value at most `u`, as a function of both arguments. -/
noncomputable def uniformTime (K δ : ℝ) (e : ℕ) (s : ℕ) (u : ℝ) : ℝ :=
  K * ((s : ℝ) ^ (3 - δ) * (Real.log s + 1) ^ e * (1 + logU u) ^ 2)

/-- **Theorem 17**, the first term of the additional time, "ν n³ log n/g".  It pays for the scans.
`κ` is the paper's ν. -/
noncomputable def termScans (n g : ℕ) (κ : ℝ) : ℝ := κ * (n : ℝ) ^ 3 * Real.log n / (g : ℝ)

/-- **Theorem 17**, the second term of the additional time, "n^{ω+o(1)} D^{3/2}".  It pays for the
choice of the prime.  `MM n` stands for the number of ring operations of the matrix multiplication,
the paper's `n^{ω+o(1)}`. -/
noncomputable def termPrime (MM : ℕ → ℝ) (n D : ℕ) : ℝ := MM n * (D : ℝ) ^ (3 / 2 : ℝ)

/-- **Theorem 17**, the third term of the additional time, "n² D g".  It pays for building the
instances. -/
noncomputable def termBuild (n D g : ℕ) : ℝ := (n : ℝ) ^ 2 * (D : ℝ) * (g : ℝ)

/-- Strassen's number of ring operations, up to a constant: `n^{log₂ 7}`. -/
noncomputable def strassen (n : ℕ) : ℝ := (n : ℝ) ^ Real.logb 2 7











/-- Proof of Theorem 19, by Corollary 26: "Let D := ⌊n^{1/18}⌋". -/
noncomputable def paramD₂₆ (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 18 : ℝ)⌋₊

/-- Proof of Theorem 19, by Corollary 26: "and g := ⌈D^{0.0315}⌉". -/
noncomputable def paramG₂₆ (n : ℕ) : ℕ := ⌈(paramD₂₆ n : ℝ) ^ (0.0315 : ℝ)⌉₊





end ThreeSumApsp


