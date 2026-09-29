-- Prove2me | Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
-- name    : HlawkaSchatten_DiagonalConstruction_ScalarBounds
-- status  : Definition
-- author  : @savarin
-- created : 2026-09-28T16:23:17.818396+00:00
-- url     : https://prove2.me/theorems/0b49f5b8-6b01-41ca-8f8d-858c72fab13f
-- title:
--   The scalar envelope bounding the normalized deficit ratio
-- statement:
--   Two scalar definitions give the sharper of two dimension-independent estimates used to confine a hypothetical strict counterexample's normalized total norm, for a real exponent $p$ and $q\in\mathbb{R}$.
--
--   `scalarEnvelopeRoot` is the following totalized expression; for $p>0$ and $q\ge0$ it is the power mean of $1$ and $q$ at exponent $p$:
--   $$
--   \operatorname{scalarEnvelopeRoot}(p,q) = \left(\frac{1+q^p}{2}\right)^{1/p}.
--   $$
--
--   `scalarEnvelope` compares the linear gap between $1$ and $q$ to twice the gap between $1$ and this power mean,
--   $$
--   \operatorname{scalarEnvelope}(p,q) = \frac{1-q}{2\big(1-\operatorname{scalarEnvelopeRoot}(p,q)\big)}.
--   $$
--
--   For $p>1$ and nonzero vectors $x,y,z$ (indexed by an arbitrary finite type) with $\|x\|_p+\|y\|_p+\|z\|_p=1$, a theorem in the same source module bounds the pair-norm sum $\|x+y\|_p+\|x+z\|_p+\|y+z\|_p$ by $2\cdot\operatorname{scalarEnvelopeRoot}\big(p,\|x+y+z\|_p\big)$. When $q=\|x+y+z\|_p<1$, this bound gives a strictly positive lower bound $2(1-\operatorname{scalarEnvelopeRoot}(p,q))$ for the pair-deficit sum. Consequently, the ratio of the triple deficit to the pair-deficit sum is at most $\operatorname{scalarEnvelope}(p,q)$. This quotient interpretation uses $q<1$; at $q=1$ the displayed definition is totalized by Lean's division convention. The same source module also proves a coarser, unconditional bound — that the triple deficit is at most $p$ times the pair-deficit sum for every exponent $p>1$, with no normalization needed — and `scalarEnvelope` is used where the sharper, normalization-dependent estimate is needed instead.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/ScalarBounds.lean#L179-L182

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sign.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Instances.Sign

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# The weighted scalar estimate for arbitrary coordinate triples

The weights are the three input norms. Applying the scalar convexity
inequality coordinate by coordinate yields the dimension-independent power
estimate used to confine a hypothetical counterexample.
-/

namespace HlawkaSchatten.DiagonalConstruction







variable {ι : Type*} [Fintype ι]













noncomputable def scalarEnvelopeRoot (p q : ℝ) : ℝ := ((1 + q ^ p) / 2) ^ (1 / p)

noncomputable def scalarEnvelope (p q : ℝ) : ℝ :=
  (1 - q) / (2 * (1 - scalarEnvelopeRoot p q))



end HlawkaSchatten.DiagonalConstruction


