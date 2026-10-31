-- Prove2me | Definitions.Def_LeastMajorized_ABMajorized
-- name    : LeastMajorized_ABMajorized
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:47:38.004912+00:00
-- url     : https://prove2.me/theorems/7c8629cc-b365-43e6-af56-e01766553e2b
-- title:
--   $(a,b)$-majorization $x\prec_{(a,b)}y$
-- statement:
--   Fix a scaling vector $a\in\mathbb R^n_{>0}$ and a shifting vector $b\in\mathbb R^n$. A vector $x\in\mathbb R^n$ is **$(a,b)$-majorized** by $y\in\mathbb R^n$, written $x\prec_{(a,b)}y$, if $x(N)=y(N)$ and, for every continuous convex function $\phi:\mathbb R\to\mathbb R$,
--
--   $$
--   \sum_{i\in N}a_i\,\phi\!\Big(\frac{x_i+b_i}{a_i}\Big)\ \le\ \sum_{i\in N}a_i\,\phi\!\Big(\frac{y_i+b_i}{a_i}\Big).
--   $$
--
--   For $a=(1,\dots,1)$ and $b=0$ this is classical majorization (Lemma 6); the shift $b$ is what makes the characterization of base polyhedra in Theorem 5 possible.
--
--   **Formalization Note** $\phi$ ranges over functions $\mathbb R\to\mathbb R$ convex on all of $\mathbb R$ and continuous, as printed. The relation is written for every $a$; every statement of the mission quantifies only over $a$ with all $a_i>0$, so Lean's convention $t/0=0$ never enters.
-- source:
--   Schoot Uiterkamp, A characterization of simultaneous optimization, majorization, and (bi)submodular polyhedra, arXiv:2201.06596v2, §3.2, p.8

import Mathlib

namespace LeastMajorized

/-- **`(a, b)`-majorization**, Schoot Uiterkamp, arXiv:2201.06596v2, §3.2, p.8: for a scaling
vector `a ∈ ℝⁿ_{>0}` and a shifting vector `b ∈ ℝⁿ`, `x` is `(a, b)`-majorized by `y`, written
`x ≺_(a,b) y`, "if `x(N) = y(N)` and for all continuous convex functions `φ` we have
`Σ_{i∈N} aᵢ φ((xᵢ + bᵢ)/aᵢ) ≤ Σ_{i∈N} aᵢ φ((yᵢ + bᵢ)/aᵢ)`."

**Formalization Note** `φ` ranges over functions `ℝ → ℝ` that are convex on all of `ℝ`
(`ConvexOn ℝ Set.univ φ`) and continuous, as printed (convexity on `ℝ` already implies
continuity). The relation is written for every `a`; the paper fixes `a ∈ ℝⁿ_{>0}`, and every
statement of the mission quantifies only over `a` with all `aᵢ > 0`, so the junk value of
`· / 0` never enters. -/
def ABMajorized {n : ℕ} (a b x y : Fin n → ℝ) : Prop :=
  ∑ i, x i = ∑ i, y i ∧
    ∀ φ : ℝ → ℝ, ConvexOn ℝ Set.univ φ → Continuous φ →
      ∑ i, a i * φ ((x i + b i) / a i) ≤ ∑ i, a i * φ ((y i + b i) / a i)

end LeastMajorized


