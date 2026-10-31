-- Prove2me | Definitions.Def_MWMSLagrange_CompSlack
-- name    : MWMSLagrange_CompSlack
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:02:28.668276+00:00
-- url     : https://prove2.me/theorems/1f979de4-9a77-480e-89c4-3b479a69aee0
-- title:
--   Conditions (3.7): $\lambda^*\ge0$, capacity, complementary slackness
-- statement:
--   Multipliers $\lambda$, base-stock levels $y$ and an allocation $\rho$ satisfy (3.7) if, for every warehouse $j$,
--
--   $$\lambda_j\ge0,\qquad \sum_{t=1}^T\sum_{i\in\mathcal N_j}\rho_{i,j}\,\mathbb E\big[(y_{i,t}-I_{i,t})^+\big]\le C_j,\qquad \lambda_j\Big(\sum_{t=1}^T\sum_{i\in\mathcal N_j}\rho_{i,j}\,\mathbb E\big[(y_{i,t}-I_{i,t})^+\big]-C_j\Big)=0,$$
--
--   where $I_{i,t}$ is the base-stock inventory under the levels $y$ with unlimited warehouses. The expected orders placed with each warehouse fit its inventory, with equality where the multiplier is positive. Algorithm 1 requires its inputs to satisfy these conditions.
-- source:
--   Miao, Jasin, Chao, Asymptotically Optimal Lagrangian Policies for Multi-Warehouse, Multi-Store Systems with Lost Sales, SSRN 3552995 (manuscript, sha256 1146a7f8…), (3.7), p.12; Algorithm 1, step 2, p.13

import Mathlib
import Definitions.Def_MWMSLagrange_Instance
import Definitions.Def_MWMSLagrange_Instance_Nset
import Definitions.Def_MWMSLagrange_demandMeasure
import Definitions.Def_MWMSLagrange_ubOnHand

open MeasureTheory

namespace MWMSLagrange

/-- Miao, Jasin, Chao, SSRN 3552995 (manuscript, sha256 1146a7f8…), (3.7), p.12: the three
conditions on `(λ^*, y^*, ρ^*)` required by Algorithm 1, step 2: for every warehouse `j`,
`λ^*_j ≥ 0`, `∑_{t=1}^T ∑_{i∈𝓝_j} ρ^*_{i,j} E[(y^*_{i,t} − I_{i,t})^+] ≤ C_j`, and
`λ^*_j · (∑_{t=1}^T ∑_{i∈𝓝_j} ρ^*_{i,j} E[(y^*_{i,t} − I_{i,t})^+] − C_j) = 0`
(complementary slackness), where `I_{i,t}` is the inventory under the base-stock levels `y^*`
(`ubOnHand`). -/
def CompSlack {M N T : ℕ} (I : Instance M N) (μ : Fin N → Fin T → Measure ℝ)
    (lam : Fin M → ℝ) (y : Fin N → Fin T → ℝ) (ρ : Fin N → Fin M → ℝ) : Prop :=
  ∀ j, 0 ≤ lam j ∧
    (∑ t : Fin T, ∑ i ∈ I.Nset j,
        ρ i j * ∫ ω, max (y i t - ubOnHand y ω i t) 0 ∂demandMeasure μ) ≤ I.C j ∧
    lam j * ((∑ t : Fin T, ∑ i ∈ I.Nset j,
        ρ i j * ∫ ω, max (y i t - ubOnHand y ω i t) 0 ∂demandMeasure μ) - I.C j) = 0

end MWMSLagrange


