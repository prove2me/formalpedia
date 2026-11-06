-- Prove2me | Definitions.Def_SilverRateLB_arcSet
-- name    : SilverRateLB_arcSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:21:17.499645+00:00
-- url     : https://prove2.me/theorems/e8764d68-48a7-4445-b6f0-3927d0d5811e
-- title:
--   The arc vectors $v(q)$ and the convex set $K$
-- statement:
--   For $\varepsilon,\gamma>0$, with $c$ and $R$ as in Lemma 2.4, the **arc vectors** are
--   $$v(q) := \bigl(p(q),-q\bigr),\qquad p(q) := \sqrt{R^2-(q+\gamma)^2},\qquad 0\le q\le 1.$$
--   They lie on the circle of radius $R$ centred at $(0,\gamma)$, from $v(0)=(c,0)$ to $v(1)=(\varepsilon,-1)$. The set $K$ is the convex hull of the origin and this arc,
--   $$K := \operatorname{conv}\bigl(\{0\}\cup\{v(q):0\le q\le1\}\bigr)\subset\mathbb R^2.$$
--   Lemma 3.1 constructs the gradient vectors of a gap as Euclidean projections onto $K$.
-- source:
--   Ye, Liu, Silver Rate Is (Almost) Optimal for Gradient Descent, arXiv:2609.09152 (sha256 6797dde3…), §3.1, p. 11; §A.1, (21), p. 20

import Mathlib
import Definitions.Def_SilverRateLB_aOf

namespace SilverRateLB

/-- **Arc vectors** (21): `v(q) := (p(q), −q)`, `p(q) := √(R² − (q + γ)²)`, `0 ≤ q ≤ 1`. They lie
on the circle of radius `R` centred at `(0, γ)`, with `v(0) = (c, 0)` and `v(1) = (ε, −1)`.

Ye, Liu, *Silver Rate Is (Almost) Optimal for Gradient Descent*, arXiv:2609.09152, §A.1, (21),
p. 20: "Set v(q) := (p(q), −q), p(q) := √(R² − (q+γ)²), 0 ≤ q ≤ 1."

**Formalization Note** `ℝ²` is `EuclideanSpace ℝ (Fin 2)`; coordinate `0` is the first. An
"arc vector" is `arcVec ε γ q` with `q ∈ [0, 1]`. -/
noncomputable def arcVec (ε γ q : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[Real.sqrt (ROf ε γ ^ 2 - (q + γ) ^ 2), -q]

/-- **The set `K`**: the convex hull of the origin and the arc `{v(q) : 0 ≤ q ≤ 1}` joining
`(c, 0)` to `(ε, −1)`.

Ye, Liu, *Silver Rate Is (Almost) Optimal for Gradient Descent*, arXiv:2609.09152, §3.1, p. 11:
"Let K be the convex hull of the origin and the shorter arc joining (c,0) to (ε,−1)"; §A.1,
p. 20: "K := conv({0} ∪ {v(q) : 0 ≤ q ≤ 1})". -/
noncomputable def arcSet (ε γ : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  convexHull ℝ ({0} ∪ (arcVec ε γ) '' Set.Icc (0 : ℝ) 1)

end SilverRateLB


