-- Prove2me | Definitions.Def_NetServicePricing_averageDegree
-- name    : NetServicePricing_averageDegree
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:36:59.229343+00:00
-- url     : https://prove2.me/theorems/ab96296e-8dbd-4803-b2c4-f6f2e4c79c10
-- title:
--   Average degree $\mathcal D=\frac1n\sum_i D_i$
-- statement:
--   The **average degree** of a network $M$ on $n$ consumers is
--
--   $$\mathcal D=\frac1n\sum_{i=1}^n D_i,$$
--
--   the mean of the weighted degrees. It measures the strength (the first-order effect) of the network externalities.
--
--   **Formalization Note** The division is real division; for $n=0$ Lean returns $0$, a case the paper never considers.
-- source:
--   Alizamir, Chen, Kim, Manshadi, Impact of Network Structure on New Service Pricing, SSRN 3236225, Definition 1, p.16

import Mathlib
import Definitions.Def_NetServicePricing_weightedDegree

namespace NetServicePricing

/-- **Average degree `D = (∑ᵢ Dᵢ)/n`.**
Alizamir, Chen, Kim, Manshadi, *Impact of Network Structure on New Service Pricing*, SSRN 3236225, Definition 1, p.16: "the average degree for a network is D = ∑_{i=1}^n Di/n".

**Formalization Note** Real division by `n`; for `n = 0` Lean's convention gives `0`, a case the
paper never considers. -/
noncomputable def averageDegree {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (∑ i, weightedDegree M i) / n

end NetServicePricing


