-- Prove2me | Definitions.Def_StrongPerfectGraph_Main_IsPerfect
-- name    : StrongPerfectGraph_Main_IsPerfect
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T12:05:42.518018+00:00
-- url     : https://prove2.me/theorems/34b0d50f-6c88-4021-9d5d-1c9aa311f576
-- title:
--   Perfect graph
-- statement:
--   A finite simple graph $G$ is **perfect** when every induced subgraph has chromatic number equal to clique number. For every vertex set $X\subseteq V(G)$,
--
--   $$\chi(G|X)=\omega(G|X).$$
--
--   Here $\chi$ is the smallest number of colors in a proper vertex coloring and $\omega$ is the maximum size of a clique. The empty induced subgraph is included, with both numbers zero. This is the paper’s notion of perfection.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 51–52, §1, definition of perfect

import Mathlib

namespace StrongPerfectGraph.Main

/-- Every induced subgraph has chromatic number equal to clique number. -/
def IsPerfect {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ X : Set V, (G.induce X).chromaticNumber = ((G.induce X).cliqueNum : ℕ∞)

end StrongPerfectGraph.Main


