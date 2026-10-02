-- Prove2me | Definitions.Def_opg37364_cut_pairs
-- name    : opg37364_cut_pairs
-- status  : Definition
-- author  : @arexychen
-- created : 2026-09-09T08:49:55.3292+00:00
-- url     : https://prove2.me/theorems/b29ba39f-a00a-4128-bbe5-460ce2ab6646
-- title:
--   Crossing pairs for a graph cut
-- statement:
--   Let $G$ be a simple graph on a vertex set $V$, and let $A\subseteq V$. The crossing-pair set is
--
--   $$\operatorname{cutPairs}(G,A)=\{(v,w)\in V\times V: v\in A,\ w\notin A,\ v\sim_G w\}.$$
--
--   Every undirected edge crossing the cut is represented once, oriented from $A$ to its complement. This provides a shared counting interface for the expansion-to-immunity step in the proof of Lemma 5. The definition imposes no expansion or graph-existence assertion.
-- source:
--   Crossing-edge notation for the expansion argument in the proof of Lemma 5, Feghali--Lucke--Paulusma--Ries, Matching Cuts in Graphs of High Girth and H-Free Graphs, Algorithmica 87 (2025), 1199--1221, https://doi.org/10.1007/s00453-025-01318-8; uses the existing Prove2Me matching-cut definition ab3f2eb8-d49e-4e0f-ba12-2055a9430b33.

import Definitions.Def_opg37364_matching_cuts

set_option autoImplicit false

namespace OPG37364

universe u

/-- Crossing pairs oriented from the chosen shore into its complement. -/
def cutPairs {V : Type u} (G : SimpleGraph V) (A : Set V) : Set (V × V) :=
  {e | e.1 ∈ A ∧ e.2 ∉ A ∧ G.Adj e.1 e.2}

end OPG37364


