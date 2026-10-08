-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Lang_WordSize
-- name    : APSPSource_ThreeSumApsp_Lang_WordSize
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T07:26:08.507318+00:00
-- url     : https://prove2.me/theorems/63c3c531-59ff-45a0-89ba-b6ee50e6b0ee
-- title:
--   Polynomial bounds in instance parameters
-- statement:
--   For natural numbers $s,k$ and a finite list of natural-number instance parameters $p_1,\ldots,p_r$, define
--
--   $$B(s,k;p_1,\ldots,p_r)=2^s\left(\prod_{i=1}^{r}(p_i+1)\right)^k.$$
--
--   The empty product is $1$. Adding one to each parameter keeps the product positive even when some parameters are zero.
--
--   This family of bounds is used to express polynomial limits on values and addresses in the structured-language development, and later to choose sufficient machine word sizes.
--
--   References:
--
--   1. [Source formalization: polynomial parameter bound](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Lang/WordSize.lean#L37-L38).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Lang/WordSize.lean#L37-L38

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
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
# A polynomial bound in the parameters fits in a word

The running-time claims hold at every word size W ≥ b (log₂ p₁ + ⋯ + log₂ p_r + 1), where p₁, …, p_r
are the parameters of the instance and the slope b is chosen with the program (`Admissible`).  A
light program states its limits as a polynomial in the parameters,
`polyBound s k params` = 2^s ((p₁ + 1) ⋯ (p_r + 1))^k.

The main fact is `polyBound_le`: this bound is at most 2^W as soon as b ≥ s + k r + k.  Each factor
p + 1 is at most 2^(log₂ p + 1) (`prod_succ_le`), so with S the sum of the logarithms the bound is
at most 2^(s + k (S + r)), and s + k (S + r) ≤ (s + k r + k) (S + 1) ≤ W.
-/

@[expose] public section

namespace Light



/-- The bound 2^s · ((p₁ + 1) (p₂ + 1) ⋯)^k in the parameters of an instance. -/
def polyBound (s k : ℕ) (params : List ℕ) : ℕ := 2 ^ s * ((params.map (· + 1)).prod) ^ k



















































































end Light


