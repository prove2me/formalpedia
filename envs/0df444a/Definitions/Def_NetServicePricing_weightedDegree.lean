-- Prove2me | Definitions.Def_NetServicePricing_weightedDegree
-- name    : NetServicePricing_weightedDegree
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:36:13.489344+00:00
-- url     : https://prove2.me/theorems/787a22f5-4852-4f50-932e-e5b46240aea2
-- title:
--   Weighted degree $D_i=\sum_j m_{ij}$
-- statement:
--   The **weighted degree** of consumer $i$ in a network $M$ is the $i$-th row sum
--
--   $$D_i=\sum_{j=1}^n m_{ij}.$$
--
--   Since $M$ is symmetric it is both the influence consumer $i$ exerts on her neighbors and the influence she receives.
-- source:
--   Alizamir, Chen, Kim, Manshadi, Impact of Network Structure on New Service Pricing, SSRN 3236225, Definition 1, p.16

import Mathlib

namespace NetServicePricing

/-- **Weighted degree `Dᵢ = ∑ⱼ mᵢⱼ`.**
Alizamir, Chen, Kim, Manshadi, *Impact of Network Structure on New Service Pricing*, SSRN 3236225, Definition 1, p.16: "The weighted degree of consumer i is Di = ∑_{j=1}^n mij".

**Formalization Note** Consumers are indexed by `Fin n`. -/
def weightedDegree {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℝ :=
  ∑ j, M i j

end NetServicePricing


