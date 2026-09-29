-- Prove2me | Definitions.Def_HlawkaSchatten_DiagonalConstruction_WeightedCoordinates
-- name    : HlawkaSchatten_DiagonalConstruction_WeightedCoordinates
-- status  : Definition
-- author  : @savarin
-- created : 2026-09-28T16:34:31.737158+00:00
-- url     : https://prove2.me/theorems/954a772e-04bf-46e0-9dea-171799876cbd
-- title:
--   Weighted coordinate norm and its reduction to a plain coordinate norm
-- statement:
--   Two total definitions describe weighted coordinate power functionals for real $p$ and real vectors indexed by an arbitrary finite type. In the positive-exponent range, nonnegative weights can be absorbed into a rescaling of the coordinates. The ordinary unweighted functional is a norm in the range $p\ge1$.
--
--   `weightedNorm` attaches a real weight $w_i$ (nonnegative in use) to each coordinate before summing:
--   $$
--   \operatorname{weightedNorm}(p,x,w) = \Big(\sum_i w_i\,|x_i|^p\Big)^{1/p}.
--   $$
--
--   `reweight` rescales each coordinate of $x$ by the corresponding weight raised to the power $1/p$:
--   $$
--   \operatorname{reweight}(p,w,x)_i = w_i^{1/p}\,x_i.
--   $$
--
--   By a theorem in the same source module, $\|\operatorname{reweight}(p,w,x)\|_p = \operatorname{weightedNorm}(p,x,w)$ for $p>0$ whenever every $w_i\ge 0$, where $\|\cdot\|_p$ is the finite coordinate power functional (`DiagonalConstruction.lpNorm`); and $\operatorname{weightedNorm}(p,x,\mathbf{1}) = \|x\|_p$ for the all-ones weight. A further theorem shows that, for fixed $x$ and $p>1$, $w\mapsto\operatorname{weightedNorm}(p,x,w)$ is concave on the nonnegative weights.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/WeightedCoordinates.lean#L16-L20

import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-! # Concavity under common coordinate reweighting -/

namespace HlawkaSchatten.DiagonalConstruction

variable {ι : Type*} [Fintype ι]

noncomputable def weightedNorm (p : ℝ) (x w : ι → ℝ) : ℝ :=
  (∑ i, w i * |x i| ^ p) ^ (1 / p)

noncomputable def reweight (p : ℝ) (w x : ι → ℝ) : ι → ℝ :=
  fun i ↦ w i ^ (1 / p) * x i













end HlawkaSchatten.DiagonalConstruction


