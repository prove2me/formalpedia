-- Prove2me | Definitions.Def_MWMSLagrange_IsAllocation
-- name    : MWMSLagrange_IsAllocation
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:02:51.811519+00:00
-- url     : https://prove2.me/theorems/96a7af65-62c3-4be0-9cf4-01effc311b84
-- title:
--   Deterministic stationary allocation $\rho_{i,j}$
-- statement:
--   An **allocation** is a family of fractions $\rho_{i,j}$ with
--
--   1. $\rho_{i,j}\in[0,1]$;
--   2. $\rho_{i,j}=0$ for $j\notin\mathcal M_i$;
--   3. $\sum_{j\in\mathcal M_i}\rho_{i,j}=1$ for every store $i$.
--
--   Store $i$ splits each of its orders among its warehouses in these proportions. By Proposition 1 such deterministic stationary allocations suffice for the relaxed problem.
-- source:
--   Miao, Jasin, Chao, Asymptotically Optimal Lagrangian Policies for Multi-Warehouse, Multi-Store Systems with Lost Sales, SSRN 3552995 (manuscript, sha256 1146a7f8…), Proposition 1, p.11; (3.5), p.12

import Mathlib
import Definitions.Def_MWMSLagrange_Instance
import Definitions.Def_MWMSLagrange_Instance_Mset

namespace MWMSLagrange

/-- Miao, Jasin, Chao, SSRN 3552995 (manuscript, sha256 1146a7f8…), Proposition 1, p.11, and
(3.5), p.12: deterministic stationary allocation fractions `ρ_{i,j}`: `ρ_{i,j} ∈ [0, 1]`,
`ρ_{i,j} = 0` for `j ∉ 𝓜_i`, and `∑_{j ∈ 𝓜_i} ρ_{i,j} = 1` for every store `i`. -/
def IsAllocation {M N : ℕ} (I : Instance M N) (ρ : Fin N → Fin M → ℝ) : Prop :=
  (∀ i j, 0 ≤ ρ i j ∧ ρ i j ≤ 1) ∧ (∀ i j, I.adj i j = false → ρ i j = 0) ∧
    (∀ i, ∑ j ∈ I.Mset i, ρ i j = 1)

end MWMSLagrange


