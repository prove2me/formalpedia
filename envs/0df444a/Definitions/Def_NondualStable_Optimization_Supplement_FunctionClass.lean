-- Prove2me | Definitions.Def_NondualStable_Optimization_Supplement_FunctionClass
-- name    : NondualStable_Optimization_Supplement_FunctionClass
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:34:19.801189+00:00
-- url     : https://prove2.me/theorems/4e0ea885-a97b-4e37-8b8d-c81cba31310b
-- title:
--   Global convex subgradient class and lower-bound profile
-- statement:
--   Let $d$ be a dimension, let $X$ be a feasible subset of $\mathbb R^d$, and let $\mathcal G$ be a set of allowed subgradients. Using the global convex subdifferential, define
--   $$
--   \mathcal F(X,\mathcal G)=\{f:\mathbb R^d\to\mathbb R:\ f\text{ is convex and }\partial f(x)\subseteq\mathcal G\text{ for every }x\in X\}.
--   $$
--   The inclusion concerns every global supporting subgradient at every feasible point, including the boundary. It imposes no Lipschitz hypothesis outside $X$. The convex subdifferential is the published DCAExtrap definition transported through the Euclidean coordinate equivalence, with the real objective embedded into the extended reals.
--
--   For $1\le p,q\le\infty$, positive integers $d,T$, and $1/\infty=0$, the accompanying rate profile is
--   $$
--   L_{p,q}(d,T)=\begin{cases}T^{-1/p+(1/q-1/2)_+},&p<q,\\ d^{1/q-1/p}T^{-1/\max\{q,2\}},&q\le p<\infty,\\1,&p=\infty.\end{cases}
--   $$
--   The $p=\infty$ branch takes precedence. This class and profile supply the input and right-hand side of the randomized local-oracle lower bound.
-- source:
--   David Martínez-Rubio, Cristóbal Guzmán, STOC 2027 submission #415 (October 2026), printed pp. 12–13,15 / PDF pp. 13–14,16, Section 7 and Theorem 13

import Mathlib
import Definitions.Def_NondualStable_Optimization_Geometry
import Definitions.Def_DCAExtrap_convexSubdiff

open scoped ENNReal

namespace NondualStable.Optimization.Supplement

/-- The global real-valued convex function class in Section 7 (PDF 13).
The published subdifferential is transported through the Euclidean coordinate equivalence.
Every global subgradient at a point of X is bounded; no condition is imposed off X. -/
def functionClass {d : ℕ} (X Gset : Set (Vec d)) : Set (Vec d → ℝ) :=
  {f | ConvexOn ℝ Set.univ f ∧ ∀ x ∈ X, ∀ g : Vec d,
    WithLp.toLp 2 g ∈ DCAExtrap.convexSubdiff
      (fun y : EuclideanSpace ℝ (Fin d) => (f (WithLp.ofLp y) : EReal))
      (WithLp.toLp 2 x) → g ∈ Gset}

/-- Theorem 13's dimension/horizon profile, including both infinity endpoints. -/
noncomputable def lowerProfile (p q : ℝ≥0∞) (d T : ℕ) : ℝ :=
  if p = ⊤ then 1
  else if p < q then (T : ℝ) ^ (-recip p + max (recip q - 1 / 2) 0)
  else (d : ℝ) ^ (recip q - recip p) * (T : ℝ) ^ (-recip (max q 2))

end NondualStable.Optimization.Supplement


