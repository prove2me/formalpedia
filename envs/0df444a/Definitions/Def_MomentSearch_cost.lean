-- Prove2me | Definitions.Def_MomentSearch_cost
-- name    : MomentSearch_cost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:09:16.542598+00:00
-- url     : https://prove2.me/theorems/a98990c8-fb92-42a7-857c-4b9fdcbcfde6
-- title:
--   Expected search cost $\mathrm{cost}_p(S)$
-- statement:
--   For a distribution $p=(p_0,\dots,p_{n-1})$ of the target on $[n]_0$ and a strategy $S$, the **expected cost** of $S$ under $p$ is
--
--   $$
--   \mathrm{cost}_p(S) := \mathbb E_{t\sim p}[q(S,t)] = \sum_{t=0}^{n-1} p_t\, q(S,t).
--   $$
--
--   **Formalization Note** A distribution is a vector $p\in\mathbb R^n$ indexed by $\mathrm{Fin}\,n$; the formula is applied to points of the simplex $\Delta_n$.
-- source:
--   Megow, Stein, Verschae, Distributionally Robust Search: The Power of Information and the Limits of Moments, arXiv:2611.04559 (held version, sha256 fbfa4b43…), §2.1, p.5 (PDF p.7)

import Mathlib
import Definitions.Def_MomentSearch_queries

namespace MomentSearch

/-- The expected cost of a strategy `S` under a distribution `p` on `[n]₀`,
`cost_p(S) := E_{t∼p}[q(S, t)] = ∑_{t=0}^{n−1} p_t q(S, t)`
(Megow, Stein, Verschae, *Distributionally Robust Search: The Power of Information and the Limits of Moments*, arXiv:2611.04559 (held version, sha256 fbfa4b43…), §2.1, p.5 (PDF p.7)).

**Formalization Note.** A distribution is a vector `p : Fin n → ℝ`; the target `t : Fin n` is
read as the natural number `t`. The formula is used for `p` in the simplex. -/
def cost {n : ℕ} (p : Fin n → ℝ) (S : Strategy n) : ℝ :=
  ∑ t : Fin n, p t * (queries S (t : ℕ) : ℝ)

end MomentSearch


