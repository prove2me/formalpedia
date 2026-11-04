-- Prove2me | Definitions.Def_ImpactCopula_genInvE
-- name    : ImpactCopula_genInvE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:53:05.448123+00:00
-- url     : https://prove2.me/theorems/2e522609-58ca-41c1-a218-d5f3cc4d8a18
-- title:
--   Extended-real inverse function $f^{-1}(y) = \inf\{x : f(x) \ge y\}$
-- statement:
--   For a non-decreasing function $f : \mathbb R \to \mathbb R$, the **inverse function** of Definition A.1 is
--
--   $$
--   f^{-1}(y) = \inf\{x \in \mathbb R : f(x) \ge y\} \in [-\infty, +\infty],
--   $$
--
--   with $\inf \emptyset = +\infty$ and the infimum of a set unbounded below equal to $-\infty$. The argument $y$ may itself be $\pm\infty$, so that $F_\theta^{-1}$ can be applied to the extended-real values of another inverse, as in Lemma 2.
--
--   **Formalization Note** The infimum is taken in `EReal`.
-- source:
--   Lo–Wu–Zhang–Zhao, Optimal Impact Portfolios with General Dependence and Marginals, SSRN 4177277 (draft of February 25, 2024), Definition A.1, p.42 (PDF p.45); used in Lemma 2, p.75 (PDF p.78)

import Mathlib

namespace ImpactCopula

/-- The inverse function of Definition A.1, Lo–Wu–Zhang–Zhao, *Optimal Impact Portfolios with General Dependence and Marginals*, SSRN 4177277 (draft of February 25, 2024), p.42 (PDF p.45), `f⁻¹(y) = inf {x : f(x) ≥ y}`,
computed in the extended reals, as the paper does when it allows the values `±∞`.

**Formalization Note.** The infimum is taken in `EReal` over the real points `x` with
`y ≤ f(x)`, for an extended-real argument `y`: the empty set gives `+∞` and a set unbounded below
gives `−∞`, the paper's convention. Used in Lemma 2 for `F_θ⁻¹` (applied to the possibly infinite
`f̲⁻¹(w)`) and for `f⁻¹`. -/
noncomputable def genInvE (f : ℝ → ℝ) (y : EReal) : EReal :=
  sInf ((fun x : ℝ => (x : EReal)) '' {x : ℝ | y ≤ (f x : EReal)})

end ImpactCopula


