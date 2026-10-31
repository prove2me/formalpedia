-- Prove2me | Definitions.Def_PCLAssort_pclEdges
-- name    : PCLAssort_pclEdges
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:17:34.424997+00:00
-- url     : https://prove2.me/theorems/962f8852-79c5-4f38-860c-739b1ed1d0d6
-- title:
--   Edge set of the reduction graph $G_z$
-- statement:
--   The reduction graph has vertex set $[n+1]$: the products $1,\dots,n$ and a dummy vertex $n+1$ that is never selected. For every ordered pair $(i,j)$ of products there are edges $(i,j)$, $(j,i)$, $(i,n+1)$ and $(j,n+1)$, so
--
--   $$
--   E=\{(i,j): i\ne j\in[n]\}\cup\{(i,n+1): i\in[n]\}.
--   $$
--
--   The dummy vertex has no outgoing edge.
--
--   **Formalization Note** Vertices are `Option (Fin n)`, with `none` the dummy vertex.
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), §3, pp.790–791 (PDF pp.6–7)

import Mathlib

namespace PCLAssort

/-- Edge set `E` of the reduction graph `G_z` (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, §3, pp.790–791): vertices `[n + 1]`, where
`n + 1` is a dummy vertex; for every ordered pair `(i, j)` of products the edges `(i, j)`, `(j, i)`,
`(i, n+1)`, `(j, n+1)`. So `E = {(i, j) : i ≠ j ∈ [n]} ∪ {(i, n+1) : i ∈ [n]}`, and the dummy has
no outgoing edge.

**Formalization Note.** Vertices are `Option (Fin n)`, with `none` the dummy vertex `n + 1` and
`some i` the product `i`. -/
def pclEdges (n : ℕ) : Finset (Option (Fin n) × Option (Fin n)) :=
  Finset.univ.filter (fun e => e.1 ≠ none ∧ e.1 ≠ e.2)

end PCLAssort


