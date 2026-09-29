-- Prove2me | Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
-- name    : HlawkaSchatten_DiagonalConstruction_Cyclic
-- status  : Definition
-- author  : @savarin
-- created : 2026-09-28T16:06:53.640924+00:00
-- url     : https://prove2.me/theorems/c4c4cf74-7f65-4cbe-85e4-1e3d1b97fdb2
-- title:
--   The cyclic comparison ratio and the cyclic constant K_p (cyclicA, cyclicB, cyclicRatio, cyclicConstant)
-- statement:
--   Four scalar definitions, for a real exponent $p$ and a real parameter $t$:
--
--   $$
--   \mathrm{cyclicA}(p,t) = (t^p+2)^{1/p}, \qquad
--   \mathrm{cyclicB}(p,t) = \big(2\,|1-t|^p + 2^p\big)^{1/p},
--   $$
--
--   $$
--   \mathrm{cyclicRatio}(p,t) = R_p(t) = \frac{3\,\mathrm{cyclicA}(p,t) - 3^{1/p}\,|2-t|}{6\,\mathrm{cyclicA}(p,t) - 3\,\mathrm{cyclicB}(p,t)},
--   $$
--
--   $$
--   \mathrm{cyclicConstant}(p) = K_p = \sup_{t\in[1/2,\,2]} R_p(t).
--   $$
--
--   For $t\ge0$, `cyclicA` and `cyclicB` are, respectively, the common `lpNorm` value of each of the three cyclic witness vectors and the common `lpNorm` value of each of their three pairwise sums (a companion bundle supplies the vectors themselves); for $p>0$ and $t\ge0$, `cyclicRatio` is the resulting ratio, for that witness triple, of a triple deficit to a pair-deficit sum; `cyclicConstant`, $K_p$, is its supremum over the fixed interval $[1/2,2]$.
--
--   For real $p>1$, $R_p$ is continuous on $[1/2,2]$ with a positive denominator throughout, so this supremum is attained there, making $K_p$ a maximum rather than merely a supremum. $K_p$ is the candidate diagonal Hlawka constant: for $p>1$ it is a necessary lower bound for any constant that works on real or complex diagonal triples in dimension at least three, and — proved elsewhere, for $p\ge256$ — it is also sufficient, making it the sharp diagonal constant in that range.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/Cyclic.lean#L20-L30

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# The cyclic comparison constant

The constant is defined from an explicit scalar formula on a fixed compact
interval. Its denominator is positive, so continuity gives an attained
maximum without presupposing the global Hlawka inequality.
-/

namespace HlawkaSchatten.DiagonalConstruction

noncomputable def cyclicA (p t : ℝ) : ℝ := (t ^ p + 2) ^ (1 / p)

noncomputable def cyclicB (p t : ℝ) : ℝ :=
  (2 * |1 - t| ^ p + (2 : ℝ) ^ p) ^ (1 / p)

noncomputable def cyclicRatio (p t : ℝ) : ℝ :=
  (3 * cyclicA p t - (3 : ℝ) ^ (1 / p) * |2 - t|) /
    (6 * cyclicA p t - 3 * cyclicB p t)

noncomputable def cyclicConstant (p : ℝ) : ℝ :=
  sSup (cyclicRatio p '' Set.Icc (1 / 2) 2)

























end HlawkaSchatten.DiagonalConstruction


