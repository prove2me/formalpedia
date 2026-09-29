-- Prove2me | Definitions.Def_HlawkaSchatten_DiagonalConstruction_HessianBounds
-- name    : HlawkaSchatten_DiagonalConstruction_HessianBounds
-- status  : Definition
-- author  : @savarin
-- created : 2026-09-28T16:17:28.426141+00:00
-- url     : https://prove2.me/theorems/cabae2e3-8f3e-47eb-8d24-15cd2d20b59e
-- title:
--   Uniform lower and upper bounds for the coordinate norm Hessian
-- statement:
--   Two explicit real-valued functions of a single real exponent $p$ supply uniform coefficients for the second directional derivative of the finite coordinate power functional (`normHessian`, defined in the `NormHessian` bundle).
--
--   `lowerHessianCoefficient` sends $p$ to
--   $$
--   \frac{(p-1)\,(43/100)^{p-2}}{3\,(157/100)^{p-1}}.
--   $$
--
--   `upperHessianCoefficient` sends $p$ to
--   $$
--   \frac{2(p-1)\,(19/50)^{p-2}}{(81/50)^{p-1}}.
--   $$
--
--   Both are ordinary real-power expressions, defined by Lean's totalized real power for every real $p$. The two Hessian-bound theorems that accompany them in the same source module assume a real exponent $p>2$: for vectors $v,h\in\mathbb{R}^3$, `lowerHessianCoefficient`$(p)$ times the squared Euclidean length of $h-a v$, with $a=\operatorname{radialCoefficient}(p,v,h)$, is a lower bound for $\operatorname{normHessian}(p,v,h)$ whenever every coordinate of $v$ has absolute value between $43/100$ and $157/100$; and $\operatorname{normHessian}(p,v,h)$ is at most `upperHessianCoefficient`$(p)$ times the plain squared Euclidean length of $h$ whenever one coordinate of $v$ has absolute value at least $81/50$ and every other coordinate has absolute value at most $19/50$. These are exactly the two coordinate patterns that arise on the cyclic coordinate box (`entryBox`, in the `Localization` bundle), where the two coefficients are used together to bound the deficit Hessian from below.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/HessianBounds.lean#L13-L17

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

/-! # Uniform lower and upper bounds for the norm Hessian -/

namespace HlawkaSchatten.DiagonalConstruction

noncomputable def lowerHessianCoefficient (p : ℝ) : ℝ :=
  (p - 1) * (43 / 100 : ℝ) ^ (p - 2) / (3 * (157 / 100 : ℝ) ^ (p - 1))

noncomputable def upperHessianCoefficient (p : ℝ) : ℝ :=
  2 * (p - 1) * (19 / 50 : ℝ) ^ (p - 2) / (81 / 50 : ℝ) ^ (p - 1)













end HlawkaSchatten.DiagonalConstruction


