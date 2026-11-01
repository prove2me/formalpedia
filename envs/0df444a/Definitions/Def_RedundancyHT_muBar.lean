-- Prove2me | Definitions.Def_RedundancyHT_muBar
-- name    : RedundancyHT_muBar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:23:45.512472+00:00
-- url     : https://prove2.me/theorems/6aaba38f-7599-44e8-8170-602fd87a5aec
-- title:
--   The average service rate $\mu=\mu_{\mathrm{tot}}/N$
-- statement:
--   The average service rate of the $N$ servers with speeds $\mu_1,\dots,\mu_N$ is
--   $$\mu=\frac{\mu_{\mathrm{tot}}}{N},\qquad \mu_{\mathrm{tot}}=\sum_{n=1}^N\mu_n.$$
--   It is the critical arrival rate of a system with local stability, and it fixes the translation between the normalized arrival rate $\lambda$ and the load of the published queue.
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, Remark 2, p.5, and text below Assumption 1, p.5

import Definitions.Def_BipartiteMatchingHT_Delay_Primitives

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **The average service rate** `µ = µ_tot / N` (arXiv:2005.14566v5, Remark 2 and §2.2, p.5). -/
def muBar {n m : ℕ} (D : Model n m) : ℝ :=
  (∑ j, D.service j) / (m : ℝ)

end RedundancyHT


