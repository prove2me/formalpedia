-- Prove2me | Definitions.Def_MomentSearch_OPT
-- name    : MomentSearch_OPT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:10:05.130587+00:00
-- url     : https://prove2.me/theorems/9f9998e3-2e61-4c75-9f7d-5a89f7fce81e
-- title:
--   Optimal expected search cost $\mathrm{OPT}(p)$
-- statement:
--   The **optimal expected search cost** of a distribution $p$ on $[n]_0$ is
--
--   $$
--   \mathrm{OPT}(p) := \min_S \mathrm{cost}_p(S),
--   $$
--
--   the minimum over all deterministic search strategies on the path. It is the benchmark of a searcher who knows $p$ exactly; the approximability factor compares every strategy against it.
--
--   **Formalization Note** Written as the infimum of $\mathrm{cost}_p(S)$ over the type of strategies on $[n]_0$. This type is nonempty for $n\ge1$ and has finitely many elements, so the infimum is attained, as the paper's minimum. For $n\ge2$ and $p\in\Delta_n$ every strategy makes at least one query on every target, so $\mathrm{OPT}(p)\ge1$ and the ratios in the approximability factor never divide by zero.
-- source:
--   Megow, Stein, Verschae, Distributionally Robust Search: The Power of Information and the Limits of Moments, arXiv:2611.04559 (held version, sha256 fbfa4b43…), §2.1, p.5 (PDF p.7)

import Mathlib
import Definitions.Def_MomentSearch_cost

namespace MomentSearch

/-- The optimal expected search cost `OPT(p) := min_S cost_p(S)`, the minimum over all
deterministic search strategies on the path (Megow, Stein, Verschae, *Distributionally Robust Search: The Power of Information and the Limits of Moments*, arXiv:2611.04559 (held version, sha256 fbfa4b43…), §2.1, p.5 (PDF p.7)).

**Formalization Note.** Written as the infimum `⨅ S : Strategy n, cost p S` in `ℝ`. For
`n ≥ 1` the strategy type is nonempty, and up to equality there are finitely many strategies on
`{0, …, n − 1}`, so the infimum is a minimum over a finite nonempty set of costs and is
attained, as in the paper. For `p` in the simplex and `n ≥ 2` every strategy makes at least one
query on every target, so `OPT p ≥ 1`. -/
noncomputable def OPT {n : ℕ} (p : Fin n → ℝ) : ℝ :=
  ⨅ S : Strategy n, cost p S

end MomentSearch


