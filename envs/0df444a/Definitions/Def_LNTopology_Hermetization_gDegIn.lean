-- Prove2me | Definitions.Def_LNTopology_Hermetization_gDegIn
-- name    : LNTopology_Hermetization_gDegIn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:21:12.306994+00:00
-- url     : https://prove2.me/theorems/58134a07-e74d-43e4-8b76-9f5207c72989
-- title:
--   Degree in an induced subgraph
-- statement:
--   For a finite simple graph $G$, a vertex set $W$ and a vertex $v$, $d_W(v)=|\{w\in W: vw\in E(G)\}|$ is the number of neighbours of $v$ in $W$. For $v\in W$ it is the degree of $v$ in the subgraph $G[W]$ induced on $W$, so "$G[W]$ has minimum degree $>d$" reads $d_W(v)>d$ for all $v\in W$.
--
--   **Formalization Note** Lemmas B.3–B.4 speak of subgraphs; a subgraph on the vertex set $W$ with minimum degree $>d$ exists if and only if the induced subgraph $G[W]$ has minimum degree $>d$, since adding edges inside $W$ only raises degrees. The mission states both lemmas for induced subgraphs.
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Topology, working paper (SSRN 4439190, February 3, 2023), Lemmas B.3–B.4, p. 12 (PDF p. 13)

import Mathlib

namespace LNTopology.Hermetization

/-- **Degree in an induced subgraph.**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Topology*, working paper
(SSRN 4439190, February 3, 2023), Lemmas B.3–B.4, p. 12 ("a subgraph H with δ(H) ≥ …", "a subgraph G′ with δ(G′) > d").

For a simple graph `G` and a vertex set `W`, `gDegIn G W v` is the number of neighbours of `v`
in `W`; for `v ∈ W` it is the degree of `v` in the subgraph induced on `W`.

**Formalization Note.** Encoding: a subgraph with minimum degree `> d` on the vertex set `W`
exists iff the induced subgraph on `W` has minimum degree `> d` (adding edges inside `W` only
raises degrees), so the mission states the lemmas for induced subgraphs. -/
def gDegIn {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) (v : V) : ℕ :=
  (W.filter (G.Adj v)).card

end LNTopology.Hermetization


