-- Prove2me | Definitions.Def_StochHiddenConvex_ComponentwiseConvexOn
-- name    : StochHiddenConvex_ComponentwiseConvexOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:50:18.022788+00:00
-- url     : https://prove2.me/theorems/283b47bc-2cb9-4400-b703-e744a8bba0be
-- title:
--   Component-wise convexity on a subset of $\mathbb R^d$
-- statement:
--   A function $h:\mathbb R^d\to\mathbb R$ is **component-wise convex** on $S\subseteq\mathbb R^d$ if for every coordinate $i$ and every $u\in S$ the one-variable function
--   $$t\longmapsto h(u_1,\dots,u_{i-1},t,u_{i+1},\dots,u_d)$$
--   is convex on the set of $t$ for which this point lies in $S$. Proposition 2.1 transfers this property from $f$ to the reformulated objective $G$; the paper's network revenue management objective is component-wise convex but not convex (Lemma G.2).
-- source:
--   X. Chen, N. He, Y. Hu, Z. Ye, Efficient Algorithms for A Class of Stochastic Hidden Convex Optimization and Its Applications in Network Revenue Management, arXiv:2205.01774v3, Proposition 2.1, p.9

import Mathlib

namespace StochHiddenConvex

/-- *Component-wise convexity* on a set `S ⊆ ℝ^d` (Chen, He, Hu & Ye, arXiv:2205.01774v3,
Proposition 2.1, p.9: "f is convex (component-wise convex)"): for every coordinate `i` and every
`u ∈ S`, the function `t ↦ h(u₁, …, u_{i−1}, t, u_{i+1}, …, u_d)` is convex on the set of `t`
for which that point lies in `S`. -/
def ComponentwiseConvexOn {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (h : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∀ i : Fin d, ∀ u ∈ S,
    ConvexOn ℝ {t : ℝ | WithLp.toLp 2 (Function.update (WithLp.ofLp u) i t) ∈ S}
      (fun t => h (WithLp.toLp 2 (Function.update (WithLp.ofLp u) i t)))

end StochHiddenConvex


