-- Prove2me | Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxGeometry
-- name    : HlawkaSchatten_DiagonalConstruction_BoxGeometry
-- status  : Definition
-- author  : @savarin
-- created : 2026-09-28T15:42:03.833573+00:00
-- url     : https://prove2.me/theorems/ee940ce1-3eda-4981-9fbc-604b8ff3a547
-- title:
--   Euclidean-square bookkeeping for triples: euclideanSq, frobeniusSq, applyTriple, totalTriple
-- statement:
--   Four definitions on vectors in $\mathbb{R}^3$ and on triples of such vectors (a `Triple` is three vectors in $\mathbb{R}^3$, packaged as $X:\mathrm{Fin}\,3\to\mathrm{Fin}\,3\to\mathbb{R}$):
--
--   1. `euclideanSq`, the squared Euclidean length of a vector $v\in\mathbb{R}^3$:
--   $$
--   \mathrm{euclideanSq}(v) = \sum_i v_i^2.
--   $$
--   2. `frobeniusSq`, the sum of `euclideanSq` over the three columns of a triple $X$ — a squared Frobenius-type size for the whole triple:
--   $$
--   \mathrm{frobeniusSq}(X) = \sum_j \mathrm{euclideanSq}(X_j).
--   $$
--   3. `applyTriple`, the linear combination of the three columns of $X$ with coefficients $a\in\mathbb{R}^3$:
--   $$
--   \mathrm{applyTriple}(X,a)_i = \sum_j a_j\, X_j\, i.
--   $$
--   4. `totalTriple`, the plain sum of the three columns:
--   $$
--   \mathrm{totalTriple}(X) = X_0+X_1+X_2.
--   $$
--
--   These are the elementary quadratic and linear tools used to measure and compare triples on the cyclic coordinate box: `euclideanSq`/`frobeniusSq` give the size estimates behind the convexity argument, `applyTriple` expresses a general linear combination of the three columns, and `totalTriple` is exactly the "$x+y+z$" argument that occurs in the Hlawka deficit of a triple.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/BoxGeometry.lean#L17-L23

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

/-!
# Quadratic geometry of the cyclic box

The joint radial estimate uses the convenient bound `300`. This weaker
intermediate constant leaves the exponent cutoff unchanged.
-/

namespace HlawkaSchatten.DiagonalConstruction

def euclideanSq (v : Fin 3 → ℝ) : ℝ := ∑ i, (v i) ^ 2

def frobeniusSq (X : Triple) : ℝ := ∑ j, euclideanSq (X j)

def applyTriple (X : Triple) (a : Fin 3 → ℝ) : Fin 3 → ℝ := fun i ↦ ∑ j, a j * X j i

def totalTriple (X : Triple) : Fin 3 → ℝ := ∑ j, X j

























end HlawkaSchatten.DiagonalConstruction


