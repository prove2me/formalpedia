-- Prove2me | Definitions.Def_NetServicePricing_completeNetwork
-- name    : NetServicePricing_completeNetwork
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:36:13.134986+00:00
-- url     : https://prove2.me/theorems/89d1c79f-96f7-42f5-a49c-6d356d745c56
-- title:
--   Complete network with average degree $\mathcal D$
-- statement:
--   The **complete network** on $n$ consumers with average degree $\mathcal D$ has every off-diagonal weight equal to $\gamma=\mathcal D/(n-1)$ and zero diagonal:
--
--   $$m_{ij}=\frac{\mathcal D}{n-1}\ (i\ne j),\qquad m_{ii}=0,$$
--
--   so that $D_i=(n-1)\gamma=\mathcal D$ for every $i$. It is balanced.
--
--   **Formalization Note** For $n=1$ there is no off-diagonal entry and the matrix is $0$.
-- source:
--   Alizamir, Chen, Kim, Manshadi, Impact of Network Structure on New Service Pricing, SSRN 3236225, §5.1, p.17

import Mathlib

namespace NetServicePricing

/-- **Complete network with average degree `D`.**
Alizamir, Chen, Kim, Manshadi, *Impact of Network Structure on New Service Pricing*, SSRN 3236225, §5.1, p.17: "a homogeneous network with a complete graph structure, in which all n
consumers exert identical influence on one another: mij = γ for all i ≠ j. This corresponds to a
network in which Di = D = (n−1)γ for all i."

The matrix with zero diagonal and every off-diagonal entry `γ = D/(n − 1)`.

**Formalization Note** For `n = 1` there are no off-diagonal entries and the matrix is `0`
(Lean's `D/0 = 0` is never used). -/
noncomputable def completeNetwork (n : ℕ) (D : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then 0 else D / ((n : ℝ) - 1)

end NetServicePricing


