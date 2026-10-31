-- Prove2me | Definitions.Def_MWMSLagrange_Instance_Nset
-- name    : MWMSLagrange_Instance_Nset
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:01:39.541632+00:00
-- url     : https://prove2.me/theorems/5383911b-e857-49c4-a713-0449688a64f4
-- title:
--   Stores $\mathcal N_j$ served by warehouse $j$
-- statement:
--   For a warehouse $j$ of an MWMS instance, $\mathcal N_j\subseteq[N]$ is the set of stores to which $j$ can deliver:
--
--   $$\mathcal N_j=\{\,i\in[N] : j\in\mathcal M_i\,\}.$$
--
--   The warehouse inventory constraint $\sum_{i\in\mathcal N_j}\sum_{t}z_{i,j,t}\le C_j$ and the Lagrangian penalty of warehouse $j$ sum over $\mathcal N_j$.
-- source:
--   Miao, Jasin, Chao, Asymptotically Optimal Lagrangian Policies for Multi-Warehouse, Multi-Store Systems with Lost Sales, SSRN 3552995 (manuscript, sha256 1146a7f8…), §2, p.6

import Mathlib
import Definitions.Def_MWMSLagrange_Instance

namespace MWMSLagrange

/-- Miao, Jasin, Chao, SSRN 3552995 (manuscript, sha256 1146a7f8…), §2, p.6: the set
`𝓝_j ⊆ [N]` of stores to which warehouse `j` can deliver inventory. -/
def Instance.Nset {M N : ℕ} (I : Instance M N) (j : Fin M) : Finset (Fin N) :=
  Finset.univ.filter fun i => I.adj i j = true

end MWMSLagrange


