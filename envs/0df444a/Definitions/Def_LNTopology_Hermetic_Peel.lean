-- Prove2me | Definitions.Def_LNTopology_Hermetic_Peel
-- name    : LNTopology_Hermetic_Peel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T08:31:43.507049+00:00
-- url     : https://prove2.me/theorems/b8b73201-0734-4c15-9ee0-25bc2448f2a3
-- title:
--   The peeling procedure of Lemma B.3 (repeatedly delete vertices of degree at most $t$)
-- statement:
--   Let $G$ be a finite simple graph with vertex set $W$ and let $t$ be a real threshold. One **peeling round** maps a vertex set $S\subseteq W$ to
--
--   $$\{v\in S:\ |N_G(v)\cap S|>t\},$$
--
--   that is, it deletes every vertex having at most $t$ neighbours in the subgraph induced on $S$. The **peeling procedure** starts from $S=W$ and performs $|W|$ rounds; its output $\mathrm{peel}(G,t)$ is the remaining vertex set.
--
--   This is the algorithm of the proof of Lemma B.3, run with the threshold $t=g_+^{-1}(2\,\mathrm{disc}(G))$ in the paper: "at each step, delete all the vertices of degree $\le t$, until there are no more vertices to remove".
--
--   **Formalization Note** Every round that changes the set removes at least one vertex, so after $|W|$ rounds no further vertex can be removed; running exactly $|W|$ rounds replaces "until there are no more vertices to remove". The threshold is an arbitrary real $t$. Subgraphs are induced subgraphs, given by their vertex sets.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Topology, SSRN 4439190 (version of Feb. 3, 2023), p. 12 (PDF p. 13), proof of Lemma B.3

import Mathlib

namespace LNTopology.Hermetic

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- One round of the peeling procedure of the proof of Lemma B.3: from the current vertex set
`S`, delete every vertex having at most `t` neighbours in `S`. -/
noncomputable def peelStep (G : SimpleGraph W) [DecidableRel G.Adj] (t : ℝ) (S : Finset W) : Finset W :=
  S.filter (fun v => t < ((G.neighborFinset v ∩ S).card : ℝ))

/-- The peeling procedure run from the whole vertex set for `|W|` rounds. -/
noncomputable def peel (G : SimpleGraph W) [DecidableRel G.Adj] (t : ℝ) : Finset W :=
  (peelStep G t)^[Fintype.card W] Finset.univ

end LNTopology.Hermetic


