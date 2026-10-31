-- Prove2me | Definitions.Def_NetServicePricing_IsNetwork
-- name    : NetServicePricing_IsNetwork
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:36:12.485789+00:00
-- url     : https://prove2.me/theorems/f68ad30d-4cbc-4f96-a692-f6ee50bfb785
-- title:
--   Network: a symmetric nonnegative weighted adjacency matrix with zero diagonal
-- statement:
--   A **network** on $n$ consumers is a real $n\times n$ matrix $M=[m_{ij}]$ of externality weights such that
--
--   1. $M$ is symmetric: $m_{ij}=m_{ji}$ for all $i,j$;
--   2. $M$ is nonnegative: $m_{ij}\ge0$ for all $i,j$;
--   3. $M$ has zero diagonal: $m_{ii}=0$ for all $i$ (self-externalities are normalized to zero).
--
--   Consumers $i$ and $j$ are neighbors when $m_{ij}>0$. This is the object every statement of the mission is about.
--
--   **Formalization Note** Consumers are indexed by `Fin n`, i.e. $0,\dots,n-1$.
-- source:
--   Alizamir, Chen, Kim, Manshadi, Impact of Network Structure on New Service Pricing, SSRN 3236225, §3.1, p.7

import Mathlib

namespace NetServicePricing

/-- **Network (weighted adjacency matrix).**
Alizamir, Chen, Kim, Manshadi, *Impact of Network Structure on New Service Pricing*, SSRN 3236225, §3.1, p.7: "These weights are assumed to be nonnegative and symmetric, i.e., mij ≥0, and
mij = mji for all i ≠ j. … self-externalities are normalized to zero, i.e., mii = 0 for all i."

A network on `n` consumers is a real `n × n` matrix `M` that is symmetric, entrywise
nonnegative and has zero diagonal.

**Formalization Note** Consumers are indexed by `Fin n` (0-based) instead of `1, …, n`. -/
def IsNetwork {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  M.IsSymm ∧ (∀ i j, 0 ≤ M i j) ∧ ∀ i, M i i = 0

end NetServicePricing


