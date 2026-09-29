-- Prove2me | Definitions.Def_HlawkaSchatten_DiagonalConstruction_Coordinates
-- name    : HlawkaSchatten_DiagonalConstruction_Coordinates
-- status  : Definition
-- author  : @savarin
-- created : 2026-09-28T16:04:17.837177+00:00
-- url     : https://prove2.me/theorems/a54e4ad8-16c8-4302-814d-5dded85aa036
-- title:
--   Coordinate permutation and coordinatewise rescaling in R^3 (orient)
-- statement:
--   For a permutation $e$ of $\{0,1,2\}$, a real vector $s=(s_0,s_1,s_2)\in\mathbb{R}^3$, and a vector $x\in\mathbb{R}^3$, `orient` defines the vector obtained by permuting $x$'s entries by $e$ and then multiplying entry $i$ by $s_i$:
--
--   $$
--   \mathrm{orient}(e,s,x)_i = s_i \cdot x_{e(i)}.
--   $$
--
--   This packages, as a single map, the symmetry used to recover a shared coordinate pattern in the diagonal construction: permuting the three coordinates and multiplying by $s$. `orient` itself places no restriction on $s$; `lpNorm` and the Hlawka deficit are unchanged under `orient` whenever every $|s_i|=1$ — a hypothesis of those invariance facts, not of `orient` itself — and it is that sign-flip case that lets a general configuration be reduced to a normal form (the cyclic sign pattern) without loss.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/Coordinates.lean#L98-L100

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

/-! # Large pair coordinates and signed coordinate permutations -/

namespace HlawkaSchatten.DiagonalConstruction









/-- A simultaneous coordinate permutation and reflection. -/
def orient (e : Equiv.Perm (Fin 3)) (s : Fin 3 → ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i ↦ s i * x (e i)







end HlawkaSchatten.DiagonalConstruction


