-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Sec4_Table2_LogBounds
-- name    : APSPSource_ThreeSumApsp_Sec4_Table2_LogBounds
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T07:49:13.818024+00:00
-- url     : https://prove2.me/theorems/4209fde2-e01f-4cdc-8fca-e3313ffa1c50
-- title:
--   Logarithm approximants and explicit error expressions
-- statement:
--   The bundle fixes real constants
--
--   $$\ell_2=0.6931471803,\quad u_2=0.6931471808,\quad \ell_3=1.0986122881,\quad u_3=1.0986122892.$$
--
--   For an integer $k$, a natural number $n$ of series terms, and a real input $\theta$, define
--
--   $$
--   x=\frac{\theta-2^k}{\theta+2^k},\qquad
--   A_{k,n}(\theta)=k\frac{\ell_2+u_2}{2}+2\sum_{i=0}^{n-1}\frac{x^{2i+1}}{2i+1},\qquad
--   E_{k,n}(\theta)=|k|\frac{u_2-\ell_2}{2}+\frac{2x^{2n}}{1-x^2}.
--   $$
--
--   These are the truncated odd-power logarithm series, with a fixed approximation to $\log 2$, and the accompanying error expression used in the source's certified numerical estimates. The constants and expressions are defined here; inequalities comparing them with actual logarithms, including the required domain hypotheses, are established separately.
--
--   References:
--
--   1. [Source formalization: constants and approximation expressions](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/Table2/LogBounds.lean#L35-L65).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/Table2/LogBounds.lean#L35-L45; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/Table2/LogBounds.lean#L53-L65

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# The numerical toolkit for Table 2

Table 2 and the proof of Corollary 26 evaluate the exponents `q(θ)` and `γ = θ ln(1/ρ_c)/ln 4` of
Corollary 31 and the bound `R_c(γ)` of (11) at rational points. All three are built from logarithms
of rational numbers. This file turns each such claim into inequalities between rational numbers,
which the tactic `numerics` checks by evaluating both sides.

* `log_mem` encloses `log θ`: write `θ = 2^k (1 + x)/(1 - x)` with `2^k` near `θ`, and sum `n` terms
  of `log ((1 + x)/(1 - x)) = 2 (x + x³/3 + x⁵/5 + ⋯)`.
* `qOf_le` and `le_qOf` bound `q(θ)` at a rational `θ`.
* `gammaOf_one_mem`, `lnΛ_zero_mem`, `lt_Rc_of_lnΛ_zero_mem` and `Rc_lt_of_lnΛ_zero_mem` treat the
  two numbers on which a row of the table depends: `ln(1/ρ_c)/ln 4` and the denominator of (11) at
  `γ = 0`.
* `Table2Query.intro`, `Table2Ninth.intro` and `Table2Density.intro` give an entry of the table from
  two rational numbers that enclose its `θ`; the `θ` itself comes from the intermediate value
  theorem.
-/

@[expose] public section

namespace ThreeSumApsp

/-! ## Logarithms of rational numbers -/

/-- Mathlib's lower bound on `ln 2 = 0.693147180559…`. -/
noncomputable def logTwoLo : ℝ := 0.6931471803

/-- Mathlib's upper bound on `ln 2 = 0.693147180559…`. -/
noncomputable def logTwoHi : ℝ := 0.6931471808

/-- A lower bound on `ln 3 = 1.098612288668…`. -/
noncomputable def logThreeLo : ℝ := 1.0986122881

/-- An upper bound on `ln 3 = 1.098612288668…`. -/
noncomputable def logThreeHi : ℝ := 1.0986122892







/-- The `x` with `θ = 2^k (1 + x)/(1 - x)`. It is small when `2^k` is near `θ`. -/
noncomputable def seriesArg (k : ℤ) (θ : ℝ) : ℝ := (θ - 2 ^ k) / (θ + 2 ^ k)

/-- The approximation `k ln 2 + 2 (x + x³/3 + ⋯)` of `log θ`, with `n` terms of the series at
`x = seriesArg k θ`, and with the midpoint of the two bounds in place of `ln 2`. -/
noncomputable def logApprox (k : ℤ) (n : ℕ) (θ : ℝ) : ℝ :=
  k * ((logTwoLo + logTwoHi) / 2)
    + 2 * ∑ i ∈ Finset.range n, seriesArg k θ ^ (2 * i + 1) / (2 * i + 1)

/-- A bound on the error of `logApprox`: `|k|` times half the distance of the two bounds on `ln 2`,
and the remainder of the series. -/
noncomputable def logErr (k : ℤ) (n : ℕ) (θ : ℝ) : ℝ :=
  |(k : ℝ)| * ((logTwoHi - logTwoLo) / 2) + 2 * (seriesArg k θ ^ (2 * n) / (1 - seriesArg k θ ^ 2))
















































/-! ## The exponent `q` of the query time (Corollary 31) -/








































/-! ## The exponent `γ` (Corollary 31) -/




















/-! ## The bound `R_c(γ)` (equation (11)) -/

























































/-! ## Entries of Table 2

An entry needs two facts on its row, `hg` (an enclosure of `ln(1/ρ_c)/ln 4`) and `hR` (the `ε` of
the row is below `R_c(γ)` up to the largest `γ` of the row), and two rational numbers `θlo ≤ θhi`
that enclose its `θ`. -/


































































end ThreeSumApsp


