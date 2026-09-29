-- Prove2me | Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxHessian
-- name    : HlawkaSchatten_DiagonalConstruction_BoxHessian
-- status  : Definition
-- author  : @savarin
-- created : 2026-09-28T15:56:37.223303+00:00
-- url     : https://prove2.me/theorems/67a497f7-8a7d-4f4f-acfa-d289c97ffb1a
-- title:
--   Second derivative of the triple Hlawka deficit along a line (deficitHessian)
-- statement:
--   For a real exponent $p$, a real constant $K$, and two triples $X, Z$ (three vectors in $\mathbb{R}^3$ each, packaged as a `Triple`), `deficitHessian` defines
--
--   $$
--   \begin{gathered}
--   \mathrm{deficitHessian}(p,K,X,Z) = (2K-1)\sum_{j} \mathrm{normHessian}_p(X_j, Z_j) \\
--   \;+\; \mathrm{normHessian}_p\Big(\sum_j X_j,\ \sum_j Z_j\Big) \;-\; K\sum_{j} \mathrm{normHessian}_p\big(\mathrm{pairTriple}(X)_j,\ \mathrm{pairTriple}(Z)_j\big),
--   \end{gathered}
--   $$
--
--   built the same way as `deficitSlope`, but from `normHessian` — for $p>4$ and a nonzero base vector, the second directional derivative of `lpNorm p` at that vector in a given direction — in place of the first derivative.
--
--   For $p>4$ and $X$ in the cyclic coordinate box, this is the second derivative at $t=0$, along the line $X+tZ$, of the same Hlawka-deficit quantity that `deficitSlope` differentiates once. `deficitHessian`'s nonnegativity throughout that box is exactly what proves the quantity convex there. Convexity is then used through Jensen's inequality over the six simultaneous permutations of vector and coordinate labels: the deficit at any point of the box is at least its value at the average of that point's six permuted images, and that average is always a positive multiple of a cyclic witness triple with parameter in $[1/2,2]$, where the deficit — for $K$ equal to the cyclic constant $K_p$ — is nonnegative by the very definition of $K_p$.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/BoxHessian.lean#L13-L16

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxCoordinates
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxGeometry
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_NormHessian
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

/-! # Nonnegative second variation on the entire cyclic box -/

namespace HlawkaSchatten.DiagonalConstruction

noncomputable def deficitHessian (p K : ℝ) (X Z : Triple) : ℝ :=
  (2 * K - 1) * (∑ j, normHessian p (X j) (Z j)) +
    normHessian p (totalTriple X) (totalTriple Z) -
      K * (∑ j, normHessian p (pairTriple X j) (pairTriple Z j))







end HlawkaSchatten.DiagonalConstruction


