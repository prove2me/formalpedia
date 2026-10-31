-- Prove2me | Definitions.Def_NetServicePricing_adjusted
-- name    : NetServicePricing_adjusted
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:36:12.164453+00:00
-- url     : https://prove2.me/theorems/f24fe8d8-265f-4d68-b90f-4cb8ec951cdb
-- title:
--   Adjusted adjacency matrix $\widehat M=M+\mu I_n$
-- statement:
--   For a network $M$ and the habit coefficient $\mu$, the **adjusted adjacency matrix** is
--
--   $$\widehat M=M+\mu I_n,$$
--
--   the network with its zero diagonal replaced by $\mu$. The consumption dynamics of the model are linear in $\widehat M$.
-- source:
--   Alizamir, Chen, Kim, Manshadi, Impact of Network Structure on New Service Pricing, SSRN 3236225, §4, p.11

import Mathlib

namespace NetServicePricing

/-- **Adjusted adjacency matrix `M̂ = M + μ Iₙ`.**
Alizamir, Chen, Kim, Manshadi, *Impact of Network Structure on New Service Pricing*, SSRN 3236225, §4, p.11: "Define adjusted adjacency matrix M̂ = M + µIn, where In is the n × n identity
matrix."

**Formalization Note** `1` is the identity matrix of `Matrix (Fin n) (Fin n) ℝ`. -/
def adjusted {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  M + μ • (1 : Matrix (Fin n) (Fin n) ℝ)

end NetServicePricing


