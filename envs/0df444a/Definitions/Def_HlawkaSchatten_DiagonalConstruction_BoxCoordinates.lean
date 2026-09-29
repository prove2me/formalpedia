-- Prove2me | Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxCoordinates
-- name    : HlawkaSchatten_DiagonalConstruction_BoxCoordinates
-- status  : Definition
-- author  : @savarin
-- created : 2026-09-28T15:38:34.735234+00:00
-- url     : https://prove2.me/theorems/da9585d5-2b76-4189-9a5a-b193e17c30f5
-- title:
--   Pairwise column sums of a triple, indexed by the omitted column (pairTriple)
-- statement:
--   For a triple $X$ of three vectors in $\mathbb{R}^3$ (a `Triple`, i.e. $X : \mathrm{Fin}\,3 \to \mathrm{Fin}\,3 \to \mathbb{R}$, so $X_j$ is the $j$-th column and $X_j\,i$ its $i$-th real entry), `pairTriple` defines the triple of pairwise sums
--
--   $$
--   \mathrm{pairTriple}(X) = (X_1+X_2,\ X_0+X_2,\ X_0+X_1),
--   $$
--
--   indexed so that entry $j$ omits column $X_j$ itself.
--
--   This packages, as another `Triple`, exactly the three pair sums (written $x+y$, $x+z$, $y+z$ when $X = (x,y,z)$) that appear in the Hlawka pair-deficit sum for a triple of vectors, so that the same per-column machinery already built for $X$ itself (`lpNorm`, `normSlope`, `normHessian`) can be reused on its pairwise sums.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/BoxCoordinates.lean#L12-L13

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
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
import Mathlib.Tactic.Abel
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

/-! # Coordinate ranges of the seven vectors on the cyclic box -/

namespace HlawkaSchatten.DiagonalConstruction

/-- Pair sums indexed by the omitted column. -/
def pairTriple (X : Triple) : Triple := ![X 1 + X 2, X 0 + X 2, X 0 + X 1]



















end HlawkaSchatten.DiagonalConstruction


