-- Prove2me | Definitions.Def_GenSort_badEdges
-- name    : GenSort_badEdges
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:26:54.544879+00:00
-- url     : https://prove2.me/theorems/d554bdb0-4440-46f1-aaa8-8255ffddad07
-- title:
--   Bad edges: edges whose orientation is mispredicted
-- statement:
--   Let $H$ be a bipartite graph with left part $L$, right part $R$ and edge set $E \subseteq L \times R$, every edge predicted to go from left to right, and let $\ell(u), r(v)$ be the original vertices of $u \in L$ and $v \in R$. An edge $(u, v)$ is **bad** if its orientation is mispredicted, i.e. $r(v) \prec_\pi \ell(u)$. The number of bad edges is $w$.
--
--   **Formalization Note** $\prec_\pi$ is strict: two copies of one original vertex never form a bad edge.
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.3, p.6 (PDF p.8)

import Mathlib

namespace GenSort

/-- **Bad edges**, Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.3, p.6 (PDF p.8): in a bipartite graph whose edges are predicted to go
from left to right, an edge `(u, v)` with `u ∈ L`, `v ∈ R` is bad if `u ≻_π v`, i.e. its
orientation is mispredicted. `ℓ` and `r` give the original vertex of a left and of a right
vertex; `w = |badEdges|`.

**Formalization Note.** `≺_π` is strict: copies of one original vertex tie and never form a bad
edge. -/
def badEdges {n : ℕ} {L R : Type*} (E : Finset (L × R)) (ℓ : L → Fin n) (r : R → Fin n)
    (π : Equiv.Perm (Fin n)) : Finset (L × R) :=
  E.filter fun p => π.symm (r p.2) < π.symm (ℓ p.1)

end GenSort


