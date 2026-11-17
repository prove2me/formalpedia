-- Prove2me | Definitions.Def_CodedSorting_Supplement_unitNetwork
-- name    : CodedSorting_Supplement_unitNetwork
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:49:45.886401+00:00
-- url     : https://prove2.me/theorems/74d41cf9-51fd-4da0-839e-b95e2c948991
-- title:
--   The unit-capacity multiple-unicast network as a multicommodity flow network
-- statement:
--   Let $G=(V,E)$ be a finite simple undirected graph on the vertex set $V=\{0,\dots,n-1\}$ (no loops, no parallel edges), carrying $W$ **unicast sessions**: session $i$ has a source $s_i$ and a sink $t_i$.
--
--   The **unit-capacity network** of $(G,s,t)$ gives every edge $\{u,v\}\in E$ capacity $c(u,v)=1$, shared by the two directions, and every non-adjacent pair capacity $0$. Its commodities are the $W$ sessions, commodity $i$ going from $s_i$ to $t_i$ with demand $1$.
--
--   A **fractional routing of common rate $\lambda$** in this network is then a feasible concurrent multicommodity flow of value $\lambda$: nonnegative arc flows $f_i(u,v)$ that send $\lambda$ units of session $i$ from $s_i$ to $t_i$, with
--   $$\sum_{i=1}^{W}\bigl(f_i(u,v)+f_i(v,u)\bigr)\le c(u,v)\qquad\text{for all }u,v,$$
--   so the capacity constraint counts both directions and all sessions. $R_{\mathrm{route}}$ is the largest such $\lambda$.
--
--   This is the routing side of Theorem 3.2.
--
--   **Formalization Note** The network is an instance of the published `GeometryOfGraphs.FlowCut.Network` and its feasibility predicate `Network.IsFeasibleFlow` is reused. That predicate is in arc form; the paper assigns flow to source–sink paths. The two forms give the same set of feasible common rates (decompose an arc flow into paths and cycles and drop the cycles).
-- source:
--   B. Li, Z. Li, S. Liu, Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting, arXiv:2610.20079 (held version, sha256 6e149d97…8850b), §3.2, p.5 (PDF 6), the network model and fractional routing

import Mathlib
import Definitions.Def_GeometryOfGraphs_FlowCut_Network

set_option autoImplicit false

namespace CodedSorting

namespace Supplement

open GeometryOfGraphs.FlowCut

open Classical in
/-- **The unit-capacity multiple-unicast network as a multicommodity flow network**
(B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory
Integer Sorting*, arXiv:2610.20079 (held version, sha256 6e149d97…8850b), §3.2, p.5 (PDF 6)).

The finite undirected network is the simple graph `G` on the vertices `Fin n` (no loops, no
parallel edges). It carries `W` unicast sessions; session `i` has source `s i` and sink `t i`.
Every edge has capacity `1`, shared by its two directions, and every non-edge capacity `0`. The
sessions are the commodities of the published network `GeometryOfGraphs.FlowCut.Network`, each
with demand `1`, so a feasible concurrent flow of value `λ` (`Network.IsFeasibleFlow`) is a
fractional routing in which every session has common rate `r_i = λ`.

**Formalization Note** The published `IsFeasibleFlow` is in arc form and bounds, for every pair
`{u, v}`, the total flow of all sessions in both directions by `C u v`; this is the paper's
"this sum includes both directions and all sessions". Arc form and the paper's path form give
the same set of feasible common rates (flow decomposition). -/
noncomputable def unitNetwork {n W : ℕ} (G : SimpleGraph (Fin n)) (s t : Fin W → Fin n) :
    Network (Fin n) where
  C := fun u v => if G.Adj u v then 1 else 0
  C_nonneg := fun u v => by split_ifs <;> norm_num
  C_symm := fun u v => by simp only [G.adj_comm]
  C_self := fun u => by simp
  k := W
  s := s
  t := t
  D := fun _ => 1
  D_nonneg := fun _ => zero_le_one

end Supplement

end CodedSorting


