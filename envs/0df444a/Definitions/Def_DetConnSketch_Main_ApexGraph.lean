-- Prove2me | Definitions.Def_DetConnSketch_Main_ApexGraph
-- name    : DetConnSketch_Main_ApexGraph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:41:25.699698+00:00
-- url     : https://prove2.me/theorems/4e18c44f-5291-46b3-9e7e-99ae53134ed5
-- title:
--   Adding a vertex $\star$ joined to every vertex (the construction of Claim 2.5)
-- statement:
--   For a graph $G$ on the vertices $\{0, \dots, n-1\}$, let $G^\star$ be the graph on $n+1$ vertices obtained by adding a new vertex $\star$ and the $n$ edges $\{\star, v\}$ for every old vertex $v$; the old vertices keep the edges of $G$. In Claim 2.5 Alice sends the connectivity message of $G_A^\star$.
--
--   **Formalization Note.** `apexGraph G : SimpleGraph (Fin (n+1))`; the old vertex $a$ is `a.castSucc` and $\star$ is `Fin.last n`. It is built with `SimpleGraph.fromRel`, which symmetrizes the relation and removes loops.
-- source:
--   Khanna, Putterman, Sudan, Deterministic Connectivity Sketches Under Edge Deletions, arXiv:2611.06626 (copy sha256 fff87f5b…), p. 15 (PDF 19), proof of Claim 2.5; p. 1 (PDF 5)

import Mathlib

namespace DetConnSketch.Main

/-!
# Adding a vertex `⋆` joined to every vertex (proof of Claim 2.5)

Khanna, Putterman, Sudan, *Deterministic Connectivity Sketches Under Edge Deletions*,
arXiv:2611.06626 (copy sha256 fff87f5b…), p. 15, Claim 2.5 and its proof; p. 1.

For a graph `G` on `Fin n`, `apexGraph G` is the graph on `Fin (n + 1)` in which the old
vertices `0, …, n - 1` (embedded by `Fin.castSucc`) carry the edges of `G`, and the new vertex
`⋆ = Fin.last n` is adjacent to every old vertex.
-/

/-- `G` on `Fin n` together with a new vertex `Fin.last n` joined to every vertex of `G`. -/
def apexGraph {n : ℕ} (G : SimpleGraph (Fin n)) : SimpleGraph (Fin (n + 1)) :=
  SimpleGraph.fromRel fun u v =>
    (∃ a b : Fin n, u = a.castSucc ∧ v = b.castSucc ∧ G.Adj a b) ∨ u = Fin.last n

end DetConnSketch.Main


