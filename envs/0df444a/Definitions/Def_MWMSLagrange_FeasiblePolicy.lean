-- Prove2me | Definitions.Def_MWMSLagrange_FeasiblePolicy
-- name    : MWMSLagrange_FeasiblePolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:02:43.772995+00:00
-- url     : https://prove2.me/theorems/2c6e0e60-dfc5-426e-a768-8c7d6cbf1902
-- title:
--   Feasible policy: $\sum_{i\in\mathcal N_j}\sum_t z_{i,j,t}\le C_j$ on every path
-- statement:
--   A **feasible policy** $\pi\in\Pi$ is a shipment policy that respects the warehouse inventories on every sample path:
--
--   $$\sum_{i\in\mathcal N_j}\sum_{t=1}^T z_{i,j,t}(\omega)\le C_j\qquad\text{for every warehouse } j \text{ and every } \omega .$$
--
--   Problem (2.1) minimizes the expected cost over these policies.
--
--   **Formalization Note** The constraint is imposed on every $\omega\in\mathbb R^{[N]\times[T]}$; changing a policy off $[0,\bar D]^{[N]\times[T]}$, where the demand law has no mass, changes no cost.
-- source:
--   Miao, Jasin, Chao, Asymptotically Optimal Lagrangian Policies for Multi-Warehouse, Multi-Store Systems with Lost Sales, SSRN 3552995 (manuscript, sha256 1146a7f8…), (2.1), p.8 (fourth constraint; "must be satisfied on each sample path")

import Mathlib
import Definitions.Def_MWMSLagrange_Instance
import Definitions.Def_MWMSLagrange_Instance_Nset
import Definitions.Def_MWMSLagrange_IsPolicy

namespace MWMSLagrange

/-- Miao, Jasin, Chao, SSRN 3552995 (manuscript, sha256 1146a7f8…), (2.1), p.8: a feasible
non-anticipating policy `π ∈ Π`: a shipment policy (`IsPolicy`) that respects the warehouse
inventory constraint `∑_{i ∈ 𝓝_j} ∑_{t=1}^T z_{i,j,t} ≤ C_j` for every warehouse `j` on every
sample path ("All the constraints in the above formulation must be satisfied on each sample
path of demands", p.8).

**Formalization Note.** The constraint is imposed on every `ω ∈ ℝ^{[N]×[T]}`, not only on
demand paths in `[0, D̄]^{[N]×[T]}`; a policy feasible on the latter can be changed off it,
where the demand law puts no mass, without changing any cost. -/
structure FeasiblePolicy {M N : ℕ} (I : Instance M N) (T : ℕ) where
  /-- the shipments `z t ω i j` from warehouse `j` to store `i` in period `t` -/
  z : Fin T → (Fin N × Fin T → ℝ) → Fin N → Fin M → ℝ
  isPolicy : IsPolicy I z
  feasible : ∀ ω j, ∑ i ∈ I.Nset j, ∑ t, z t ω i j ≤ I.C j

end MWMSLagrange


