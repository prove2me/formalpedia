-- Prove2me | Definitions.Def_TermCycDich_Outcome
-- name    : TermCycDich_Outcome
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:42:41.536758+00:00
-- url     : https://prove2.me/theorems/0fe2584a-b3ed-4dba-aa58-eb7fb619c42b
-- title:
--   Outcomes of Theorem 1.2
-- statement:
--   The **outcomes** of the algorithm of Theorem 1.2 on a graph with vertices $0,\dots,n-1$ are of three kinds:
--
--   1. the claim "$\mathrm{bidim}(G,R)>b$";
--   2. a vertex set $S$, standing for the induced subgraph $G_0 = G[S]$ to keep;
--   3. a tree $T$ on nodes $0,\dots,m-1$ with bags $\beta(t)\subseteq V(G)$, standing for a tree-decomposition.
--
--   What each outcome asserts is the separate definition `OutcomeCorrect`.
-- source:
--   Bentert–Cavallaro–Wiederrecht, A Dichotomy for Terminal Cyclability, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), Theorem 1.2, p.4 (PDF 6)

import Mathlib

namespace TermCycDich

/-- The **outcomes of the algorithm of Theorem 1.2** on an annotated graph with vertex set
`Fin n`.

Bentert–Cavallaro–Wiederrecht, *A Dichotomy for Terminal Cyclability*, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), Theorem 1.2, p.4 (PDF 6): "finds one of the following outcomes [...]: i) bidim(G, R) > b,
ii) an induced subgraph G_0 with R ⊆ V(G_0) [...], or iii) a tree-decomposition for G [...]".

**Formalization Note** `bidimGt` is outcome (i); `keep S` is outcome (ii), the induced subgraph
`G_0 = G[S]` given by its vertex set `S`; `treeDec m T bag` is outcome (iii), a tree `T` on
`Fin m` with bags `bag t ⊆ V(G)`. What each outcome asserts is `OutcomeCorrect`. -/
inductive Outcome (n : ℕ) where
  /-- outcome (i): `bidim(G, R) > b` -/
  | bidimGt : Outcome n
  /-- outcome (ii): the vertex set `S = V(G_0)` of the induced subgraph to keep -/
  | keep (S : Finset (Fin n)) : Outcome n
  /-- outcome (iii): a tree `T` on `Fin m` and its bags -/
  | treeDec (m : ℕ) (T : SimpleGraph (Fin m)) (bag : Fin m → Finset (Fin n)) : Outcome n

end TermCycDich


