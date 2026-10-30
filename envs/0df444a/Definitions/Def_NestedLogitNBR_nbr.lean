-- Prove2me | Definitions.Def_NestedLogitNBR_nbr
-- name    : NestedLogitNBR_nbr
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:36:08.822756+00:00
-- url     : https://prove2.me/theorems/429ce341-daf0-4983-b814-a4d16f2f50a9
-- title:
--   Nested-by-revenue assortment $N_{ij}=\{1,\dots,j\}$
-- statement:
--   Since the products of each nest are ordered by decreasing revenue $r_{i1}\ge\dots\ge r_{in}$, the assortment of the $j$ products with the largest revenues is
--
--   $$
--   N_{ij}=\{1,2,\dots,j\},\qquad j\in N_+=\{0,1,\dots,n\},\qquad N_{i0}=\emptyset .
--   $$
--
--   These nested-by-revenue assortments are the candidate assortments of the linear program (4) in Theorem 7, and the sets over which the performance factor (6) is computed.
--
--   **Formalization Note** Products are `Fin n`, $0$-based, so $N_{ij}$ is the set of Lean products $k$ with $k<j$; it does not depend on $i$.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014, doi:10.1287/opre.2014.1256), §3, pp. 13-14 (N_ij, N_i0 = ∅, N_+)

import Mathlib

namespace NestedLogitNBR

/-- **Nested-by-revenue assortment `N_ij = {1, …, j}`.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript dated June 18, 2013 (published as Operations Research 62(2), 2014,
doi:10.1287/opre.2014.1256), §3, pp. 13–14: "we use `N_ij` to denote the nested-by-revenue assortment that includes
the first `j` products with the largest revenues in nest `i`. In other words, we have
`N_ij = {1, 2, …, j}` for all `i ∈ M`, `j ∈ N`. For notational uniformity, we also let
`N_i0 = ∅` and `N_+ = N ∪ {0}`."

`nbr j` is the set of the first `j` products, for `j ∈ N_+ = {0, …, n}`.

**Formalization Note.** Products are `Fin n`, 0-based: the paper's products `1, …, j` are the
Lean products `k` with `k.val < j`. So `nbr 0 = ∅`, `nbr n = Finset.univ`, and `nbr j` has
`j` elements for `j ≤ n`. The set does not depend on the nest `i`, since the products of every
nest are indexed in decreasing order of revenue (p. 7). -/
def nbr {n : ℕ} (j : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun k => k.val < j)

end NestedLogitNBR


