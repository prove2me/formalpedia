-- Prove2me | Definitions.Def_MWMSLagrange_postLevel
-- name    : MWMSLagrange_postLevel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:03:45.12381+00:00
-- url     : https://prove2.me/theorems/980578e4-b984-4ab9-bd5c-b7bc2a50e41b
-- title:
--   Post-delivery level $y_{i,t}=I_{i,t}+\sum_{j}z_{i,j,t}$
-- statement:
--   The inventory level of store $i$ in period $t$ after replenishment arrives is
--
--   $$y_{i,t}=I_{i,t}+\sum_{j\in\mathcal M_i}z_{i,j,t}.$$
--
--   The period cost of store $i$ is $h_i(y_{i,t}-D_{i,t})^+ + b_i(D_{i,t}-y_{i,t})^+$.
-- source:
--   Miao, Jasin, Chao, Asymptotically Optimal Lagrangian Policies for Multi-Warehouse, Multi-Store Systems with Lost Sales, SSRN 3552995 (manuscript, sha256 1146a7f8…), §2, p.8 (definition of y^π_{i,t})

import Mathlib
import Definitions.Def_MWMSLagrange_Instance
import Definitions.Def_MWMSLagrange_Instance_Mset
import Definitions.Def_MWMSLagrange_onHand

namespace MWMSLagrange

/-- Miao, Jasin, Chao, SSRN 3552995 (manuscript, sha256 1146a7f8…), §2, p.8: the inventory
level `y^π_{i,t} = I_{i,t} + ∑_{j ∈ 𝓜_i} z_{i,j,t}` of store `i` in period `t` after the
replenishment arrives (zero lead time). -/
noncomputable def postLevel {M N T : ℕ} (I : Instance M N)
    (z : Fin T → (Fin N × Fin T → ℝ) → Fin N → Fin M → ℝ) (ω : Fin N × Fin T → ℝ)
    (i : Fin N) (t : Fin T) : ℝ :=
  onHand I z ω i t + ∑ j ∈ I.Mset i, z t ω i j

end MWMSLagrange


