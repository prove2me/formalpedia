-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Theorem21b_NegativeTriangle
-- name    : APSPSource_ThreeSumApsp_Sec3_Theorem21b_NegativeTriangle
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T07:24:44.669877+00:00
-- url     : https://prove2.me/theorems/c85b9480-2bec-4a52-9e86-944410a1eac3
-- title:
--   Prefix-weight transformations from negative to exact triangles
-- statement:
--   For natural numbers $x,y,v,\ell$, define the difference of binary prefixes
--
--   $$G_\ell(x,y,v)=\left\lfloor\frac{2v}{2^\ell}\right\rfloor-\left\lfloor\frac{2x}{2^\ell}\right\rfloor-\left\lfloor\frac{2y}{2^\ell}\right\rfloor.$$
--
--   For a nonnegative integer bound $U$, level $\ell$, and integer $e$, the bundle defines three transformations on edge weights. If the original weights $a,b,c$ lie in $[-U,U]$, put $x=a+U$, $y=b+U$, and $v=2U-c$. The transformed weights are
--
--   $$a'=\left\lfloor\frac{2x}{2^\ell}\right\rfloor,\qquad b'=\left\lfloor\frac{2y}{2^\ell}\right\rfloor,\qquad c'=e-\left\lfloor\frac{2v}{2^\ell}\right\rfloor.$$
--
--   These formulas provide the individual transformed instances used in the negative-triangle reduction. The choice of levels and values $e$, and correctness of the complete reduction, belong to subsequent theorems.
--
--   **Formalization Note** The transformations are total on all integer weights: conversion to a natural number replaces a negative shifted value by zero before the division. The displayed formulas use the intended bounded-weight domain, where the shifted values are nonnegative.
--
--   References:
--
--   1. [Source formalization: prefix gap](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec3/Theorem21b/NegativeTriangle.lean#L31-L34).
--   2. [Source formalization: edge-weight transformations](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec3/Theorem21b/NegativeTriangle.lean#L105-L113).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec3/Theorem21b/NegativeTriangle.lean#L31-L34; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec3/Theorem21b/NegativeTriangle.lean#L105-L113

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Theorem 21(b): Negative Triangle reduces to Exact Triangle

[VW13, Theorem 3.3] in the form needed for Theorem 21(b): one question about a negative triangle
becomes `O(log U)` questions about a zero triangle.  Shifting the weights turns "the triangle is
negative" into `x + y < v` for natural numbers (`S_neg_iff`).  Let the gap at level `ℓ` be
`⌊2v/2^ℓ⌋ - ⌊2x/2^ℓ⌋ - ⌊2y/2^ℓ⌋` (`prefixGap`).  If `x + y < v`, the gap at level 0 is
`2(v - x - y) ≥ 2`, which is why the numbers are doubled; from one level to the next a gap of at
least 4 stays at least 2, and the gap is below 2 once `2^ℓ > v`.  So at some level the gap is
exactly 2 or exactly 3, and conversely a gap of at least 2 gives `x + y < v`
(`lt_iff_exists_prefixGap`).  "The gap is `e`" is an exact condition on a triangle (`negToExact`,
`negToExact_isZeroTriangle_iff`).  Together: `hasNegativeTriangle_iff` and
`theorem_21b_negative_to_exact`.
-/

@[expose] public section

namespace ThreeSumApsp

namespace Theorem21

/-- The gap at level `ℓ`: the difference `⌊2v/2^ℓ⌋ - ⌊2x/2^ℓ⌋ - ⌊2y/2^ℓ⌋` of the prefixes of `2v`,
`2x` and `2y`. -/
 def prefixGap (x y v ℓ : ℕ) : ℤ :=
  ((2 * v / 2 ^ ℓ : ℕ) : ℤ) - ((2 * x / 2 ^ ℓ : ℕ) : ℤ) - ((2 * y / 2 ^ ℓ : ℕ) : ℤ)






































































/-- The Exact Triangle instance for the level `ℓ` and the exact value `e`.  The weights `w(a,b)`,
`w(b,c)` and `w(a,c)` in `[-U, U]` are first shifted to the natural numbers `x = w(a,b) + U`,
`y = w(b,c) + U` and `v = 2U - w(a,c)`, so that the triangle is negative exactly if `x + y < v`;
then `x` and `y` are replaced by the prefixes `⌊2x/2^ℓ⌋` and `⌊2y/2^ℓ⌋`, and `v` by `e - ⌊2v/2^ℓ⌋`.
-/
def negToExact (U ℓ : ℕ) (e : ℤ) : (ℤ → ℤ) × (ℤ → ℤ) × (ℤ → ℤ) :=
  (fun wAB => ((2 * (wAB + U).toNat / 2 ^ ℓ : ℕ) : ℤ),
    fun wBC => ((2 * (wBC + U).toNat / 2 ^ ℓ : ℕ) : ℤ),
    fun wAC => e - ((2 * (2 * U - wAC).toNat / 2 ^ ℓ : ℕ) : ℤ))





































































end Theorem21




































end ThreeSumApsp


