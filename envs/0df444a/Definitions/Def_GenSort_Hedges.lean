-- Prove2me | Definitions.Def_GenSort_Hedges
-- name    : GenSort_Hedges
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:29:37.392869+00:00
-- url     : https://prove2.me/theorems/c6bba0f7-1bb5-4e3b-ac85-e5471748f459
-- title:
--   The bipartite prediction graph $H = (L \cup R, F)$
-- statement:
--   Given a split of the $\sigma$-oriented edges of $F$, the **bipartite prediction graph** $H$ has one edge for every edge of $F$: the oriented edge $(u, v)$ joins the left copy $(u, i)$ to the right copy $(v, j)$, where $i$ and $j$ are its group indices at $u$ and at $v$. A vertex of $H$ is a pair (original vertex, copy index); the edges of $H$ correspond one-to-one to the edges of $F$.
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.2, p.6 (PDF p.8)

import Mathlib
import Definitions.Def_GenSort_orient
import Definitions.Def_GenSort_Split

namespace GenSort

/-- **The bipartite prediction graph `H = (L ∪ R, F)`**, Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.2, p.6 (PDF p.8): its edges join
the left copy `(u, lc (u,v))` to the right copy `(v, rc (u,v))` for each `σ`-oriented edge
`(u, v)` of `F`. A vertex of `H` is a pair (original vertex, copy index); `σ` predicts every edge
to go from `L` to `R`. -/
noncomputable def Hedges {n : ℕ} {F : Finset (Sym2 (Fin n))} {σ : Equiv.Perm (Fin n)} {d : ℕ}
    (sp : Split F σ d) : Finset ((Fin n × Fin n) × (Fin n × Fin n)) :=
  (orient F σ).image fun p => ((p.1, sp.lc p), (p.2, sp.rc p))

end GenSort


