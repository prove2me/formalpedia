-- Prove2me | Definitions.Def_AgnosticTNS_cut
-- name    : AgnosticTNS_cut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:33:09.655944+00:00
-- url     : https://prove2.me/theorems/eec1faeb-0da7-4900-a648-6fcd45de0a1f
-- title:
--   Cut $\mathrm{cut}_G(S)$ of a vertex set
-- statement:
--   For a finite simple graph $G=([n],E)$ and a vertex set $S\subseteq[n]$, the **cut** of $S$ is the set of edges with exactly one endpoint in $S$:
--   $$
--   \mathrm{cut}_G(S) := \{\{u,v\}\in E : u\in S,\ v\notin S\}.
--   $$
--   Its size $|\mathrm{cut}_G(S)|$ controls the Schmidt rank of tensor network states across the bipartition $S \mid [n]\setminus S$.
--
--   **Formalization Note** Vertices are `Fin n` (0-based); the cut is a finite set of edges of $G$, each counted once.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Section 2.1, Eq. (2.1), p.11

import Mathlib

namespace AgnosticTNS

/-- **The cut of a vertex set**, Eq. (2.1), p.11 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)):
`cut_G(S) := {{u, v} ∈ E : u ∈ S, v ∉ S}`, the edges of `G` with exactly one endpoint in `S`.

**Formalization Note** Vertices are `Fin n` (the paper's `[n]`, 0-based). The cut is a finite set of
edges of `G` (elements of `G.edgeSet`), each edge counted once. -/
noncomputable def cut {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Finset G.edgeSet := by
  classical
  exact Finset.univ.filter fun e => ∃ u ∈ S, ∃ v ∉ S, e.1 = s(u, v)

end AgnosticTNS


