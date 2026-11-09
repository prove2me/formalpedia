-- Prove2me | Definitions.Def_NAMatchEst_rowNbrs
-- name    : NAMatchEst_rowNbrs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:51:38.135764+00:00
-- url     : https://prove2.me/theorems/6ecf5084-52ef-4642-826f-5d26080d00ae
-- title:
--   Labels revealed by a full row
-- statement:
--   From the neighbour answers of a run, the set of labels revealed by the first $D$ positions of the adjacency list of $v$: the vertices $u$ with $\mathrm{nbr}(v,i)=u$ for some $1\le i\le D$. For $v\in U$ and $D=\Delta$ this is all of $N(v)$.
--
--   **Formalization Note** An unasked query and the answer $\bot$ reveal no label.
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.2, p.20 (PDF 24)

import Mathlib

namespace NAMatchEst

/-- The labels revealed by the first `D` positions of the adjacency list of `v`, read from the
neighbour answers `m`: the vertices `u` with `m v i = u` for some `1 ≤ i ≤ D`.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.2, p.20 (PDF 24): "For every vertex of U, the first ∆ positions of its adjacency list
reveal its entire neighbourhood. … A full row therefore tells us all neighbours of a retained
vertex".

**Formalization Note** `m v i = some (some u)` means the query `nbr(v, i)` was made and answered
`u`; `some none` is the answer `⊥`, and `none` an unasked query. -/
noncomputable def rowNbrs {n : ℕ} (m : Fin n → ℕ → Option (Option (Fin n))) (v : Fin n)
    (D : ℕ) : Finset (Fin n) :=
  open Classical in Finset.univ.filter fun u => ∃ i ∈ Finset.Icc 1 D, m v i = some (some u)

end NAMatchEst


