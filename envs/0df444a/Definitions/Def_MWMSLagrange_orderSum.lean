-- Prove2me | Definitions.Def_MWMSLagrange_orderSum
-- name    : MWMSLagrange_orderSum
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:02:57.406725+00:00
-- url     : https://prove2.me/theorems/cd269b20-94ed-4851-ae18-34cd2d26ee86
-- title:
--   Weighted base-stock orders $f_j$ at warehouse $j$
-- statement:
--   For a warehouse $j$, levels $y_{i,t}$ and fractions $\rho_{i,j}$,
--
--   $$f_j(\omega)=\sum_{i\in\mathcal N_j}\sum_{t=1}^T\rho_{i,j}\,(y_{i,t}-I_{i,t})^+$$
--
--   is the total quantity the base-stock policy orders from $j$ on the demand path $\omega$ when warehouses are unlimited ($I$ the base-stock inventory). It depends only on the demands at the stores of $\mathcal N_j$. Its expectation is the left side of the capacity condition in (3.7), and its excess over $C_j$ is what can go unserved in the real system.
-- source:
--   Miao, Jasin, Chao, Asymptotically Optimal Lagrangian Policies for Multi-Warehouse, Multi-Store Systems with Lost Sales, SSRN 3552995 (manuscript, sha256 1146a7f8…), proof of Theorem 2, p.24 (definition of f_j)

import Mathlib
import Definitions.Def_MWMSLagrange_Instance
import Definitions.Def_MWMSLagrange_Instance_Nset
import Definitions.Def_MWMSLagrange_ubOnHand

namespace MWMSLagrange

/-- Miao, Jasin, Chao, SSRN 3552995 (manuscript, sha256 1146a7f8…), proof of Theorem 2, p.24:
`f_j(𝒟_j) = ∑_{i∈𝓝_j} ∑_{t=1}^T ρ_{i,j} (y_{i,t} − I_{i,t})^+`, the `ρ`-weighted total base-stock
orders placed with warehouse `j` on the demand path `ω` in the system with unlimited warehouse
inventory (`I = ubOnHand y`). The page writes it for `(y^*, ρ^*)`; here the levels and
fractions are arguments. It depends on `ω` only through the demands of the stores in `𝓝_j`. -/
noncomputable def orderSum {M N T : ℕ} (I : Instance M N) (y : Fin N → Fin T → ℝ)
    (ρ : Fin N → Fin M → ℝ) (j : Fin M) (ω : Fin N × Fin T → ℝ) : ℝ :=
  ∑ i ∈ I.Nset j, ∑ t : Fin T, ρ i j * max (y i t - ubOnHand y ω i t) 0

end MWMSLagrange


