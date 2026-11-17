-- Prove2me | Definitions.Def_QGChasing_Supplement_phi
-- name    : QGChasing_Supplement_phi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:24:30.758992+00:00
-- url     : https://prove2.me/theorems/d013f8e7-6fae-4045-a47d-c81387dc6ee2
-- title:
--   $\phi(q)=\min_{0\le\delta<1}\Lambda(q,\delta)$, Eq. (2)
-- statement:
--   For $q>0$,
--   $$
--   \phi(q)=\min_{0\le\delta<1}\Lambda(q,\delta),
--   $$
--   with $\Lambda$ from Eq. (2). The interval is half-open: $\delta=0$ is allowed and $\delta=1$ is excluded. The paper shows that $\phi$ is continuous and strictly decreasing on $(0,\infty)$ with $\frac1{q(q+1)}\le\phi(q)\le\frac1{q^2}$, so $\phi(q)=\lambda$ has a unique positive solution $q^*(\lambda)$ for every $\lambda>0$.
--
--   **Formalization Note** Defined as the infimum of the values $\Lambda(q,\delta)$, $\delta\in[0,1)$. For $q>0$ this set is nonempty and bounded below by $0$, so the infimum is a genuine real infimum. That the minimum is attained is a result of the paper (Lemma 5.2), not part of the definition.
-- source:
--   He–Yang–Jiang–Zhang, Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth, STOC 2027 submission (manuscript sha256 ba253cd3…02239), Eq. (2), p.2; Lemma 5.2, p.11

import Mathlib
import Definitions.Def_QGChasing_Supplement_bigLambda

namespace QGChasing.Supplement

/-- `ϕ(q) = min_{0 ≤ δ < 1} Λ(q, δ)`, Eq. (2) (He–Yang–Jiang–Zhang, *Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth*, STOC 2027 submission manuscript (sha256 ba253cd3…02239), p.2).

**Formalization Note** Written as the infimum of `Λ(q, ·)` over the half-open interval `[0, 1)`.
For `q > 0` this set of values is nonempty and bounded below by `0` (every value is positive), so
the infimum is a genuine real infimum, not a junk value; that it is attained (so that the source's
`min` is meaningful) is part of Lemma 5.2 and is not built into the definition. -/
noncomputable def phi (q : ℝ) : ℝ :=
  sInf (bigLambda q '' Set.Ico (0 : ℝ) 1)

end QGChasing.Supplement


