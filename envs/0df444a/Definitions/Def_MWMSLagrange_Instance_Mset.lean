-- Prove2me | Definitions.Def_MWMSLagrange_Instance_Mset
-- name    : MWMSLagrange_Instance_Mset
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:01:38.465556+00:00
-- url     : https://prove2.me/theorems/b86bd812-a079-4849-a376-49df9522d2ce
-- title:
--   Warehouses $\mathcal M_i$ that can replenish store $i$
-- statement:
--   For a store $i$ of an MWMS instance, $\mathcal M_i\subseteq[M]$ is the set of warehouses that can ship to $i$:
--
--   $$\mathcal M_i=\{\,j\in[M] : \text{store } i \text{ can be replenished from warehouse } j\,\}.$$
--
--   It indexes the shipping decisions $z_{i,j,t}$, $j\in\mathcal M_i$, and the allocation constraint $\sum_{j\in\mathcal M_i}\rho_{i,j}=1$.
-- source:
--   Miao, Jasin, Chao, Asymptotically Optimal Lagrangian Policies for Multi-Warehouse, Multi-Store Systems with Lost Sales, SSRN 3552995 (manuscript, sha256 1146a7f8…), §2, p.6

import Mathlib
import Definitions.Def_MWMSLagrange_Instance

namespace MWMSLagrange

/-- Miao, Jasin, Chao, SSRN 3552995 (manuscript, sha256 1146a7f8…), §2, p.6: the set
`𝓜_i ⊆ [M]` of warehouses that can replenish store `i`. -/
def Instance.Mset {M N : ℕ} (I : Instance M N) (i : Fin N) : Finset (Fin M) :=
  Finset.univ.filter fun j => I.adj i j = true

end MWMSLagrange


