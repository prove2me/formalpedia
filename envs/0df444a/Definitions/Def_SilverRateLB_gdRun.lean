-- Prove2me | Definitions.Def_SilverRateLB_gdRun
-- name    : SilverRateLB_gdRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:20:17.053589+00:00
-- url     : https://prove2.me/theorems/a4c21e23-ea9e-4989-9fc0-3a6742c32b7b
-- title:
--   Gradient descent with a predetermined stepsize schedule
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$ and let $H=(h_1,\dots,h_n)$ be a stepsize schedule fixed in advance. **Gradient descent** from $x_0$ produces
--   $$x_t = x_{t-1} - h_t\nabla f(x_{t-1}),\qquad 1\le t\le n,$$
--   and this definition returns the final iterate $x_n$.
--
--   **Formalization Note** The schedule is a list read left to right, so the intermediate iterate $x_t$ is the run on the first $t$ stepsizes. $\nabla$ is Mathlib's gradient, the true gradient whenever $f$ is differentiable, as in every theorem that uses it.
-- source:
--   Ye, Liu, Silver Rate Is (Almost) Optimal for Gradient Descent, arXiv:2609.09152 (sha256 6797dde3…), §1, p. 3

import Mathlib

namespace SilverRateLB

/-- **Gradient descent with a predetermined stepsize schedule.** `gdRun f H x₀` is the iterate
`x_n` obtained from `x₀` by the updates `x_t = x_{t−1} − h_t ∇f(x_{t−1})`, `1 ≤ t ≤ n`, where
`H = (h_1, …, h_n)`.

Ye, Liu, *Silver Rate Is (Almost) Optimal for Gradient Descent*, arXiv:2609.09152, §1, p. 3:
"Given a stepsize schedule H = (h1, ..., hn) ∈ [0,∞)^n fixed before the optimization begins, GD
proceeds via the iteration xt = xt−1 − ht∇f(xt−1), 1 ≤ t ≤ n."

**Formalization Note** The schedule is a `List ℝ` read left to right (position `t` of the list,
1-based, is `h_t`), so the intermediate iterate `x_t` is `gdRun f (H.take t) x₀`. `ℝ^d` is
`EuclideanSpace ℝ (Fin d)` and `∇` is Mathlib's `gradient`; every theorem that uses `gdRun`
assumes `f` differentiable, so `gradient f` is the true gradient. -/
noncomputable def gdRun {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (H : List ℝ)
    (x₀ : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  H.foldl (fun x h => x - h • gradient f x) x₀

end SilverRateLB


