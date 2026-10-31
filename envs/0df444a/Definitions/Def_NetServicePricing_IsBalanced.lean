-- Prove2me | Definitions.Def_NetServicePricing_IsBalanced
-- name    : NetServicePricing_IsBalanced
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:37:59.546798+00:00
-- url     : https://prove2.me/theorems/5a72ed49-7a4d-4ea3-98b2-90f8ec426606
-- title:
--   Balanced network
-- statement:
--   A network is **balanced** if every consumer has the same weighted degree, equal to the average degree:
--
--   $$D_i=\mathcal D\qquad\text{for all }1\le i\le n.$$
--
--   Balanced networks are the homogeneous ones; the complete network with equal weights is one example, but there are many others.
-- source:
--   Alizamir, Chen, Kim, Manshadi, Impact of Network Structure on New Service Pricing, SSRN 3236225, Definition 1, p.16

import Mathlib
import Definitions.Def_NetServicePricing_weightedDegree
import Definitions.Def_NetServicePricing_averageDegree

namespace NetServicePricing

/-- **Balanced network.**
Alizamir, Chen, Kim, Manshadi, *Impact of Network Structure on New Service Pricing*, SSRN 3236225, Definition 1, p.16: "a network is called balanced if Di = D for all 1 ≤ i ≤ n."

Every weighted degree equals the network's own average degree. -/
def IsBalanced {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i, weightedDegree M i = averageDegree M

end NetServicePricing


