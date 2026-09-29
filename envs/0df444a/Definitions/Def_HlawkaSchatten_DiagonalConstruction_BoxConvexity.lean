-- Prove2me | Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxConvexity
-- name    : HlawkaSchatten_DiagonalConstruction_BoxConvexity
-- status  : Definition
-- author  : @savarin
-- created : 2026-09-28T15:52:54.619422+00:00
-- url     : https://prove2.me/theorems/149cc404-d435-4c1c-a983-20fc6a0ef285
-- title:
--   First derivative of the triple Hlawka deficit along a line (deficitSlope)
-- statement:
--   For a real exponent $p$, a real constant $K$, and two triples $X, Z$ (each a `Triple`, i.e. three vectors in $\mathbb{R}^3$ packaged as `Fin 3 → Fin 3 → ℝ`), `deficitSlope` defines
--
--   $$
--   \begin{gathered}
--   \mathrm{deficitSlope}(p,K,X,Z) = (2K-1)\sum_{j} \mathrm{normSlope}_p(X_j, Z_j) \\
--   \;+\; \mathrm{normSlope}_p\Big(\sum_j X_j,\ \sum_j Z_j\Big) \;-\; K\sum_{j} \mathrm{normSlope}_p\big(\mathrm{pairTriple}(X)_j,\ \mathrm{pairTriple}(Z)_j\big),
--   \end{gathered}
--   $$
--
--   where `normSlope` is, for $p>1$ and a nonzero base vector, the directional derivative of `lpNorm p` at that vector in a given direction, and `pairTriple` returns the three pairwise column sums of a triple.
--
--   For $p>1$, and at any $X$ whose three columns, three pairwise column sums and column total are all nonzero (as they are throughout the cyclic coordinate box), this is exactly the derivative at $t=0$, along the line $X + tZ$, of the quantity $K\cdot(\text{pair-deficit sum}) - (\text{triple deficit})$ built from `lpNorm p` on the three columns of $X$: the quantity whose nonnegativity on a box around the cyclic sign matrix (the cyclic witness triple at parameter $t=1$) shows $K$ is a valid Hlawka constant there. `deficitSlope` is the first-order tool for that convexity argument; its own derivative, `deficitHessian`, is what actually gets checked for a sign.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/BoxConvexity.lean#L15-L18

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxCoordinates
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxGeometry
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_NormHessian
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sign.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Order.Compact

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-! # Convexity of the sharp deficit on the cyclic box -/

namespace HlawkaSchatten.DiagonalConstruction

noncomputable def deficitSlope (p K : ℝ) (X Z : Triple) : ℝ :=
  (2 * K - 1) * (∑ j, normSlope p (X j) (Z j)) +
    normSlope p (totalTriple X) (totalTriple Z) -
      K * (∑ j, normSlope p (pairTriple X j) (pairTriple Z j))

















end HlawkaSchatten.DiagonalConstruction


