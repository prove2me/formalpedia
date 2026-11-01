-- Prove2me | Definitions.Def_AdditiveConvexity_IsAdditivelyConvexOn
-- name    : AdditiveConvexity_IsAdditivelyConvexOn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:21.467139+00:00
-- url     : https://prove2.me/theorems/c6c2c9e1-baea-4d7d-a1b9-53672aa5ef71
-- title:
--   Additive convexity on a convex set
-- statement:
--   Let $V$ be a convex subset of $\mathbb R^\iota$ for a finite index set $\iota$. A function $f$ is **additively convex** on $V$ if there are functions $\varphi_i:\mathbb R\to\mathbb R$, $i\in\iota$, with
--   $$
--   f(x)=\sum_{i\in\iota}\varphi_i(x_i)\qquad\text{for every }x\in V,
--   $$
--   each $\varphi_i$ being convex on the projection $\{x_i : x\in V\}$ of $V$ on coordinate $i$. The module also names the data $\varphi$ of such a decomposition, `IsAdditiveConvexDecomposition`.
--
--   This is the structural property that decomposes a multivariate value function into univariate convex functions.
--
--   **Formalization Note** Definition 1 says "univariate convex functions" without naming a domain. The domain here is the coordinate projection of $V$, because the paper uses functions that are convex only there: its $f_0$ in (EC.21) is convex only on $(-\infty,0]$. The functions are total in Lean; nothing is asserted off $V$ and off the projections.
-- source:
--   Gong–Wang, Preservation of Additive Convexity, SSRN 3217007 (accepted manuscript), Definition 1, p.2 (PDF p.2)

import Mathlib

namespace AdditiveConvexity

/-- `φ` is an additive convex decomposition of `f` on `V`: every `φ i` is a convex function of one
real variable on the projection of `V` on coordinate `i`, and `f x = ∑ i, φ i (x i)` for `x ∈ V`.
The data of Definition 1 of Gong–Wang, Preservation of Additive Convexity, SSRN 3217007 (accepted
manuscript), Definition 1, p.2 (PDF p.2).

**Formalization Note.** Definition 1 says "univariate convex functions" without giving their
domain; the convexity domain is the coordinate projection `(fun x => x i) '' V`, not all of `ℝ`
(the paper's `f₀` in (EC.21), p.ec11, PDF p.28, is convex only on `(-∞, 0]`). `f` and the `φ i`
are total functions; nothing is asserted about their values off `V` and off the projections. -/
def IsAdditiveConvexDecomposition {ι : Type*} [Fintype ι] (V : Set (ι → ℝ))
    (f : (ι → ℝ) → ℝ) (φ : ι → ℝ → ℝ) : Prop :=
  (∀ i, ConvexOn ℝ ((fun x : ι → ℝ => x i) '' V) (φ i)) ∧ ∀ x ∈ V, f x = ∑ i, φ i (x i)

/-- **Additive convexity.** `f` is additively convex on the convex set `V`: Gong–Wang, Preservation
of Additive Convexity, SSRN 3217007 (accepted manuscript), Definition 1, p.2 (PDF p.2).

**Formalization Note.** The convexity of `V`, a presupposition of Definition 1, is the first
conjunct. See `IsAdditiveConvexDecomposition` for the domain of the univariate functions. -/
def IsAdditivelyConvexOn {ι : Type*} [Fintype ι] (V : Set (ι → ℝ)) (f : (ι → ℝ) → ℝ) : Prop :=
  Convex ℝ V ∧ ∃ φ : ι → ℝ → ℝ, IsAdditiveConvexDecomposition V f φ

end AdditiveConvexity


