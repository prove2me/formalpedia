-- Prove2me | Definitions.Def_LeviSampling_BaseStock_AlphaPoint
-- name    : LeviSampling_BaseStock_AlphaPoint
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:48:22.748319+00:00
-- url     : https://prove2.me/theorems/78d91d4d-fed3-4477-8a84-01eec1948724
-- title:
--   α-point of a convex function (Definition 3.3, p. 833)
-- statement:
--   **Definition 3.3** (p. 833), in dimension one. A point $y$ is an **$\alpha$-point** of $f : \mathbb R \to \mathbb R$ if $f$ has a subgradient at $y$ of absolute value at most $\alpha$:
--   $$\exists\, r \in \mathbb R,\quad |r| \le \alpha \quad\text{and}\quad f(z) \ge f(y) + r(z - y) \ \text{ for all } z \in \mathbb R.$$
--   An $\alpha$-point is an approximate first-order optimality point; for $\alpha = 0$ it is a global minimizer.
--
--   **Formalization Note** The paper's definition is for $f : \mathbb R^m \to \mathbb R$ with the $\ell_1$ norm; only $m = 1$ is used in §3, where the norm is $|r|$. The paper says "less than $\alpha$" in words and writes $\le \alpha$ in the formula; the formula (used by the proof of Lemma 3.3) is followed.
-- source:
--   Levi, Roundy & Shmoys, Provably Near-Optimal Sampling-Based Policies for Stochastic Inventory Control Models, Math. Oper. Res. 32(4) 2007, p. 833, Definition 3.3

import Mathlib

namespace LeviSampling.BaseStock

/-- **Definition 3.3** (p. 833), in dimension one. A point `y` is an **`α`-point** of
`f : ℝ → ℝ` if `f` has a subgradient `r` at `y` with `|r| ≤ α`, i.e. there is `r` with `|r| ≤ α`
and `f z ≥ f y + r (z - y)` for every `z`. -/
def IsAlphaPoint (f : ℝ → ℝ) (α y : ℝ) : Prop :=
  ∃ r : ℝ, |r| ≤ α ∧ ∀ z, f y + r * (z - y) ≤ f z

end LeviSampling.BaseStock


