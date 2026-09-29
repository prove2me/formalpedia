-- Prove2me | Definitions.Def_LogRegretOCO_FTAL_IsFTLRun
-- name    : LogRegretOCO_FTAL_IsFTLRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T21:38:06.145633+00:00
-- url     : https://prove2.me/theorems/bafc5fbe-dea3-4614-a6aa-f229fc3d9654
-- title:
--   Follow the Leader run (§3.3)
-- statement:
--   Let $P \subseteq \mathbb{R}^n$ be a decision set and let $f_1, f_2, \dots$ be cost functions on $\mathbb{R}^n$. A sequence of points $x_1, x_2, \dots$ is a run of **Follow the Leader** (FTL) on $f$ over $P$ if, for every round $t \ge 1$,
--
--   $$
--   x_t \in P \quad\text{and}\quad \sum_{\tau=1}^{t-1} f_\tau(x_t) \le \sum_{\tau=1}^{t-1} f_\tau(y) \quad \text{for all } y \in P,
--   $$
--
--   that is, $x_t \in \arg\min_{x \in P} \sum_{\tau=1}^{t-1} f_\tau(x)$: the player plays the point that would have been best on all the rounds seen so far. In round $1$ the sum is empty, so $x_1$ is an arbitrary point of $P$.
--
--   Follow the Leader is the basic online algorithm that the paper's Follow the Approximate Leader runs on surrogate costs; Theorem 5 of the paper bounds its regret on costs of the form $g_t(v_t^\top x)$.
--
--   **Formalization Note** Rounds are $1$-based and $x_0$ is unused. Points live in `EuclideanSpace ℝ (Fin n)`. The argmin is encoded as a predicate on the whole trajectory, not as a chosen minimiser, so every tie-breaking rule among minimisers gives a run.
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Mach Learn 69 (2007), p. 179, §3.3 ("choosing x_t = argmin_{x∈P} Σ_{τ=1}^{t−1} f_τ(x)")

import Mathlib

namespace LogRegretOCO.FTAL

/-- Follow the Leader (Hazan–Agarwal–Kale 2007, §3.3, p. 179): `x` is a run of FTL on the cost
functions `f` over the decision set `P` if, for every round `t ≥ 1`, the point `x t` lies in `P`
and minimises the cumulative cost of the rounds `1, …, t - 1` over `P`. Rounds are 1-based and
`x 0` is unused. At `t = 1` the sum is empty, so `x 1` is an arbitrary point of `P`. Any
tie-breaking rule among minimisers gives a run. -/
def IsFTLRun {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n)))
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ t : ℕ, 1 ≤ t →
    x t ∈ P ∧ ∀ y ∈ P, ∑ τ ∈ Finset.Ico 1 t, f τ (x t) ≤ ∑ τ ∈ Finset.Ico 1 t, f τ y

end LogRegretOCO.FTAL


