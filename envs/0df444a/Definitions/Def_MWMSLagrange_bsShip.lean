-- Prove2me | Definitions.Def_MWMSLagrange_bsShip
-- name    : MWMSLagrange_bsShip
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:01:20.57824+00:00
-- url     : https://prove2.me/theorems/8087d5af-1823-42fb-9e13-f8d53baca0cd
-- title:
--   Base-stock shipments $\rho_{i,j}(y_{i,t}-I_{i,t})^+$
-- statement:
--   The base-stock policy with levels $y_{i,t}$ and allocation $\rho_{i,j}$, run with unlimited warehouse inventory, ships
--
--   $$z_{i,j,t}=\rho_{i,j}\,(y_{i,t}-I_{i,t})^+$$
--
--   from warehouse $j$ to store $i$ in period $t$, where $I_{i,t}$ is the base-stock inventory above.
-- source:
--   Miao, Jasin, Chao, Asymptotically Optimal Lagrangian Policies for Multi-Warehouse, Multi-Store Systems with Lost Sales, SSRN 3552995 (manuscript, sha256 1146a7f8…), Algorithm 1, steps 2–3, p.13; p.21 (the hypothetical system)

import Mathlib
import Definitions.Def_MWMSLagrange_ubOnHand

namespace MWMSLagrange

/-- Miao, Jasin, Chao, SSRN 3552995 (manuscript, sha256 1146a7f8…), Algorithm 1 and p.21: the
shipments of the base-stock policy with levels `y_{i,t}` and allocation `ρ_{i,j}` in the system
with unlimited warehouse inventory: `z_{i,j,t} = ρ_{i,j} (y_{i,t} − I_{i,t})^+`, with
`I = ubOnHand y`. -/
noncomputable def bsShip {M N T : ℕ} (y : Fin N → Fin T → ℝ) (ρ : Fin N → Fin M → ℝ) :
    Fin T → (Fin N × Fin T → ℝ) → Fin N → Fin M → ℝ :=
  fun t ω i j => ρ i j * max (y i t - ubOnHand y ω i t) 0

end MWMSLagrange


