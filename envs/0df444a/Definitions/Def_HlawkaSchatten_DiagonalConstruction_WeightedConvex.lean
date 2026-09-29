-- Prove2me | Definitions.Def_HlawkaSchatten_DiagonalConstruction_WeightedConvex
-- name    : HlawkaSchatten_DiagonalConstruction_WeightedConvex
-- status  : Definition
-- author  : @savarin
-- created : 2026-09-28T16:31:06.894006+00:00
-- url     : https://prove2.me/theorems/185b05ec-6ace-4b41-8892-86871a0b87b2
-- title:
--   Weighted pair and total sums for a three point convexity inequality
-- statement:
--   Two definitions frame a weighted three-point convexity inequality for an arbitrary function $f:\mathbb{R}\to\mathbb{R}$ and real weights $a,b,c$. The definitions are totalized when a denominator vanishes; the convexity inequality described below uses strictly positive weights.
--
--   `weightedPairs` sums, over the three pairs among three real numbers $x,y,z$, the combined weight of the pair times $f$ at the pair's weighted average:
--   $$
--   \begin{gathered}
--   \operatorname{weightedPairs}(f,a,b,c,x,y,z) = (a+b)\,f\!\Big(\frac{ax+by}{a+b}\Big) \\
--   + (a+c)\,f\!\Big(\frac{ax+cz}{a+c}\Big) + (b+c)\,f\!\Big(\frac{by+cz}{b+c}\Big).
--   \end{gathered}
--   $$
--
--   `weightedTotal` sums the three individually weighted values of $f$ and one further term, the combined weight times $f$ at the overall weighted average:
--   $$
--   \operatorname{weightedTotal}(f,a,b,c,x,y,z) = a f(x)+b f(y)+c f(z) + (a+b+c)\,f\!\Big(\frac{ax+by+cz}{a+b+c}\Big).
--   $$
--
--   A theorem in the same source module shows $\operatorname{weightedPairs}(f,a,b,c,x,y,z) \le \operatorname{weightedTotal}(f,a,b,c,x,y,z)$ whenever $f$ is convex on all of $\mathbb{R}$ and $a,b,c>0$, by an elementary chord argument that orders the three points, without representing $f$ as an integral of absolute-value functions. Applied entrywise with $f(t)=|t|^p$ (in the `ScalarBounds` bundle), this is the scalar convexity engine that produces the dimension-independent power estimate used to confine a hypothetical counterexample.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/WeightedConvex.lean#L68-L77

import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# A weighted three-point convexity inequality

The scalar input to the sharp construction is a weighted Hlawka inequality
for any convex function on the real line. The proof uses chords and orders
the three points; it needs no integral representation of convex functions.
-/

namespace HlawkaSchatten.DiagonalConstruction







/-- The weighted pair-sum functional. -/
noncomputable def weightedPairs (f : ℝ → ℝ) (a b c x y z : ℝ) : ℝ :=
  (a + b) * f ((a * x + b * y) / (a + b)) +
    (a + c) * f ((a * x + c * z) / (a + c)) +
    (b + c) * f ((b * y + c * z) / (b + c))

/-- The weighted singleton and total functional. -/
noncomputable def weightedTotal (f : ℝ → ℝ) (a b c x y z : ℝ) : ℝ :=
  a * f x + b * f y + c * f z +
    (a + b + c) * f ((a * x + b * y + c * z) / (a + b + c))













end HlawkaSchatten.DiagonalConstruction


