-- Prove2me | Definitions.Def_HlawkaSchatten_DiagonalConstruction_Sparsification
-- name    : HlawkaSchatten_DiagonalConstruction_Sparsification
-- status  : Definition
-- author  : @savarin
-- created : 2026-09-28T16:25:35.832487+00:00
-- url     : https://prove2.me/theorems/fa98b750-5564-40f5-8c67-b691fba21853
-- title:
--   The feasible set of nonnegative weights with fixed linear moments
-- statement:
--   `momentFiber` is the set of nonnegative weight vectors, indexed by an arbitrary finite type $\iota$, satisfying three prescribed linear moment constraints: given a moment assignment $A:\iota\to(\{0,1,2\}\to\mathbb{R})$ and a target $b:\{0,1,2\}\to\mathbb{R}$,
--   $$
--   \operatorname{momentFiber}(A,b) = \Big\{\, w:\iota\to\mathbb{R} \ \Big|\ (\forall i,\ w_i\ge 0)\ \text{and}\ \big(\forall k\in\{0,1,2\},\ \textstyle\sum_i w_i\,A(i,k) = b(k)\big) \,\Big\}.
--   $$
--
--   This is the feasible set for the three-coordinate reduction step of the sharp diagonal construction. A theorem in the same source module shows that, when $A$ has nonnegative entries with every row sum $\sum_k A(i,k)$ positive (so the fiber is compact) and $F$ is continuous and concave on the nonnegative orthant $\{w\mid\forall i,\ w_i\ge0\}$, every $w_0\in\operatorname{momentFiber}(A,b)$ is matched by some $w\in\operatorname{momentFiber}(A,b)$ with $F(w)\le F(w_0)$ and at most three nonzero coordinates. In the intended use, $A(i,\cdot)$ records the moments contributed by coordinate $i$ toward three fixed pair power sums of a coordinate triple, and $b$ holds their target values while the weights are varied; the definition itself is stated for an arbitrary moment matrix $A$ and target $b$, with no reference to power sums.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/Sparsification.lean#L28-L29

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Compact

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Three constraints admit a sparse concave minimizer

For nonnegative coordinate weights, fixing three positive linear moments
gives a compact feasible set. Minimize the concave objective, then maximize
the sum of squared weights among its minimizers. A supported kernel
direction would produce two feasible perturbations whose average squared
size is strictly larger. Thus at most three weights are positive.
-/

namespace HlawkaSchatten.DiagonalConstruction

variable {ι : Type*} [Fintype ι]

def momentFiber (A : ι → Fin 3 → ℝ) (b : Fin 3 → ℝ) : Set (ι → ℝ) :=
  {w | (∀ i, 0 ≤ w i) ∧ ∀ k, ∑ i, w i * A i k = b k}







end HlawkaSchatten.DiagonalConstruction


