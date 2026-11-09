-- Prove2me | Definitions.Def_NAMatchEst_RandAlg_run
-- name    : NAMatchEst_RandAlg_run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:52:08.87529+00:00
-- url     : https://prove2.me/theorems/981eedf5-33c1-4ea7-9010-d81d17794c22
-- title:
--   Running a non-adaptive algorithm on a graph
-- statement:
--   The output of a non-adaptive algorithm $A$ on an adjacency-list graph $G$ under a seed $\omega$: every query in $\mathrm{queries}(\omega)$ is answered by the oracles of $G$ ($\deg(v)$ is the length of the list of $v$, $\mathrm{nbr}(v,i)$ the neighbour oracle), every other query is hidden, and the output rule is applied to the seed and these answers.
--
--   The output therefore depends on the graph only through the answers to the queries the seed fixed in advance.
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §2.1, p.13 (PDF 17)

import Mathlib
import Definitions.Def_NAMatchEst_AdjList
import Definitions.Def_NAMatchEst_AdjList_nbr
import Definitions.Def_NAMatchEst_RandAlg

namespace NAMatchEst

/-- The output of the non-adaptive algorithm `A` on the adjacency-list graph `G` under seed `ω`:
every query in `A.queries ω` is answered by the oracles of `G` (`deg(v)` = length of the list of
`v`, `nbr(v, i)` = `AdjList.nbr`), every other query is hidden (`none`), and `A.output` is applied.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §2.1, p.13 (PDF 17) (degree and neighbour oracles; non-adaptivity).

**Formalization Note** The answers are computed only after the whole query list is fixed by the
seed, which is the source's non-adaptivity. -/
def RandAlg.run {n : ℕ} {β : Type} (A : RandAlg n β) (G : AdjList n) (ω : A.Ω) : β :=
  A.output ω
    (fun v => if Query.deg v ∈ A.queries ω then some (G.adj v).length else none)
    (fun v i => if Query.nbr v i ∈ A.queries ω then some (G.nbr v i) else none)

end NAMatchEst


