-- Prove2me | Definitions.Def_MarketplaceScalability_Params_q
-- name    : MarketplaceScalability_Params_q
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:47:50.552754+00:00
-- url     : https://prove2.me/theorems/a49e249b-14fc-4031-ad7b-4b2d676a1e77
-- title:
--   The first-order-condition output $q(\tilde c)$
-- statement:
--   The output determined by the first-order condition: $q(\tilde c)$ is the point of $J$ with
--   $$
--   (1-\alpha)\,D(q(\tilde c))=\tilde c.
--   $$
--   It is the output of a seller whose service has marginal cost $\tilde c$.
--
--   **Formalization Note** $q$ is a partial inverse of $x\mapsto(1-\alpha)D(x)$ on $J$, written with `Function.invFunOn`. It is meaningful where the condition has a solution in $J$, in particular on $(0,\bar c]$. Elsewhere it is an arbitrary value, so the comparisons that read $q$ at a platform price test $p\le\bar c$ first.
-- source:
--   Li, Pisano, Xu & Zhu, Marketplace Scalability and Strategic Use of Platform Investment, SSRN 3310484, §2.4, p.6

import Mathlib
import Definitions.Def_MarketplaceScalability_Params_J

namespace MarketplaceScalability

/-- The output `q(c̃)` determined by the first-order condition `(1 − α) D(q(c̃)) = c̃`.
Li, Pisano, Xu & Zhu, *Marketplace Scalability and Strategic Use of Platform Investment*, SSRN 3310484, §2.4, p.6.

**Formalization Note** `q` is a partial inverse of `x ↦ (1 − α) D x` on `J`, written with
`Function.invFunOn`. It is meaningful at the costs `c̃` for which the first-order condition has
a solution in `J`, in particular on `(0, c̄]`; elsewhere `invFunOn` returns an arbitrary value, so
every comparison below that reads `q` at a platform price tests `p ≤ c̄` first. -/
noncomputable def Params.q (P : Params) (ct : ℝ) : ℝ :=
  Function.invFunOn (fun x => (1 - P.α) * P.D x) P.J ct

end MarketplaceScalability


