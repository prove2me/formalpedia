-- Prove2me | Definitions.Def_HlawkaSchatten_DiagonalConstruction_TailEstimates
-- name    : HlawkaSchatten_DiagonalConstruction_TailEstimates
-- status  : Definition
-- author  : @savarin
-- created : 2026-09-28T16:27:53.096379+00:00
-- url     : https://prove2.me/theorems/3497e90c-7b18-4f16-b464-67e42b1c52e5
-- title:
--   The explicit cyclic witness parameter and its uniform estimates
-- statement:
--   `constructionParameter` is the explicit cyclic-witness parameter, written so that rational bounds on $\log$ and $\exp$ can be applied to it directly:
--   $$
--   \operatorname{constructionParameter}(p) = \exp\!\Big(-\frac{\log p}{p}\Big).
--   $$
--
--   For $p>0$, this equals $p^{-1/p}$. The exponential formula defines the parameter for every real $p$ using Lean's totalized logarithm and division; the power identity is asserted only on the positive domain.
--
--   For $p\ge 256$, theorems in the same source module show $\operatorname{constructionParameter}(p)\in[1/2,1]$, and use it as the parameter $t$ in the cyclic ratio $R_p(t)$ (`cyclicRatio`): the value $R_p\big(\operatorname{constructionParameter}(p)\big)$ exceeds the common intermediate quantity $\tfrac{939}{2000}p$. Since $K_p$ (`cyclicConstant`) is at least $R_p(t)$ for every $t$ in $[1/2,2]$, this shows $K_p>\tfrac{939}{2000}p$. The same intermediate quantity is also shown to exceed the value of the scalar envelope (`scalarEnvelope`, from the `ScalarBounds` bundle) at $53/150$; together, these two separating estimates force a hypothetical strict counterexample's normalized total norm below $53/150$.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/TailEstimates.lean#L51-L52

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sign.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Order.Compact

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Explicit uniform estimates above the cutoff

Rational logarithm bounds separate the cyclic witness and scalar envelope
at the common intermediate value `939 * p / 2000`.
-/

namespace HlawkaSchatten.DiagonalConstruction









/-- The explicit cyclic parameter, written using `exp` for its estimates. -/
noncomputable def constructionParameter (p : ℝ) : ℝ := Real.exp (-(Real.log p * p⁻¹))































end HlawkaSchatten.DiagonalConstruction


