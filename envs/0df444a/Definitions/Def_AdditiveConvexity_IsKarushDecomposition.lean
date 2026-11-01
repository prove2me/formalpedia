-- Prove2me | Definitions.Def_AdditiveConvexity_IsKarushDecomposition
-- name    : AdditiveConvexity_IsKarushDecomposition
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:22.341461+00:00
-- url     : https://prove2.me/theorems/91b26768-e2a1-4c25-be39-594ab6d081af
-- title:
--   Karush decomposition of a convex function
-- statement:
--   Let $A,B\subseteq\mathbb R$ and $\varphi,G,H:\mathbb R\to\mathbb R$. The pair $(G,H)$ is a **Karush decomposition** of $\varphi$ on $A$ with right ends in $B$ if $G$ is convex and increasing on $A$, $H$ is convex and decreasing on $B$, and for all $a\in A$, $b\in B$ with $a\le b$, whenever the minimum of $\varphi$ over $A\cap[a,b]$ exists,
--   $$
--   \min_{\theta\in A\cap[a,b]}\varphi(\theta)=G(a)+H(b).
--   $$
--   This is the conclusion of Karush's lemma, which separates the two ends of the interval.
--
--   **Formalization Note** The minimum is expressed with `IsLeast`. The definition does not assert that the minimum exists: for a convex function it can fail to (on $[0,1]$, $\varphi(0)=1$, $\varphi(t)=t$ for $t>0$), and the identity is required for every pair at which it does. The printed lemma has $B=A$; the use in (EC.2) takes right ends that may lie above $A$.
-- source:
--   Gong–Wang, Preservation of Additive Convexity, SSRN 3217007 (accepted manuscript), Lemma EC.1, p.ec1 (PDF p.18)

import Mathlib

namespace AdditiveConvexity

/-- The conclusion of Karush's lemma for `φ` on `A` with right ends in `B`: `G` is convex and
increasing on `A`, `H` is convex and decreasing on `B`, and for `a ∈ A`, `b ∈ B` with `a ≤ b`,
every minimum of `φ` over `A ∩ [a, b]` equals `G a + H b`. Gong–Wang, Preservation of Additive
Convexity, SSRN 3217007 (accepted manuscript), Lemma EC.1, p.ec1 (PDF p.18).

**Formalization Note.** `min` is `IsLeast` of the image. The printed `min_{x≤θ≤y} f(θ)` need not
exist (on `[0, 1]`, `f 0 = 1`, `f t = t` for `t > 0` has none), so the identity is required pair by
pair for each minimum that exists; no existence of a minimum is part of this definition. The set
`B` of right ends is `A` in the printed lemma; the use in (EC.2) has `b = y₁`, which may lie above
`A`. -/
def IsKarushDecomposition (A B : Set ℝ) (φ G H : ℝ → ℝ) : Prop :=
  ConvexOn ℝ A G ∧ MonotoneOn G A ∧ ConvexOn ℝ B H ∧ AntitoneOn H B ∧
    ∀ a ∈ A, ∀ b ∈ B, a ≤ b → ∀ v : ℝ, IsLeast (φ '' (A ∩ Set.Icc a b)) v → v = G a + H b

end AdditiveConvexity


