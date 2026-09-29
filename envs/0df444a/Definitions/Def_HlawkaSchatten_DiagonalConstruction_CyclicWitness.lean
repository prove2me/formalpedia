-- Prove2me | Definitions.Def_HlawkaSchatten_DiagonalConstruction_CyclicWitness
-- name    : HlawkaSchatten_DiagonalConstruction_CyclicWitness
-- status  : Definition
-- author  : @savarin
-- created : 2026-09-28T16:09:57.943534+00:00
-- url     : https://prove2.me/theorems/b133e9d0-f5d4-4f10-a5b7-5606fd77c319
-- title:
--   The three explicit cyclic witness vectors in R^3 (cyclicX, cyclicY, cyclicZ)
-- statement:
--   For a real parameter $t$, three explicit vectors in $\mathbb{R}^3$:
--
--   $$
--   \mathrm{cyclicX}(t) = (-t,\,1,\,1), \qquad
--   \mathrm{cyclicY}(t) = (1,\,-t,\,1), \qquad
--   \mathrm{cyclicZ}(t) = (1,\,1,\,-t).
--   $$
--
--   These vectors witness the cyclic comparison ratio $R_p(t)$ (`cyclicRatio`). For $t\ge0$, each has the same `lpNorm` value ($\mathrm{cyclicA}(p,t)$); for every real $t$, their three pairwise sums also have a common value ($\mathrm{cyclicB}(p,t)$). For $p>0$ and $t\ge0$, their triple deficit and pair-deficit sum therefore give the scalar formulas defining $R_p(t)$. For $p>0$, padding with zero coordinates preserves these norms. Thus the same witness works in every dimension at least three and, for $p>1$, makes $K_p=\sup_{t\in[1/2,2]}R_p(t)$ a necessary lower bound for any constant valid in such a dimension.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/CyclicWitness.lean#L19-L21

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Fin.VecNotation
import Mathlib.Topology.Order.Compact

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Cyclic witnesses and the necessary lower bound

The three cyclic vectors have equal norms and their ratio is the scalar
formula defining the comparison constant. Zero padding preserves all seven
norms, so the lower bound holds in every dimension at least three.
-/

namespace HlawkaSchatten.DiagonalConstruction

def cyclicX (t : ℝ) : Fin 3 → ℝ := ![-t, 1, 1]
def cyclicY (t : ℝ) : Fin 3 → ℝ := ![1, -t, 1]
def cyclicZ (t : ℝ) : Fin 3 → ℝ := ![1, 1, -t]

























end HlawkaSchatten.DiagonalConstruction


