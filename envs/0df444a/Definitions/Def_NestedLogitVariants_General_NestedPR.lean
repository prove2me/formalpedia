-- Prove2me | Definitions.Def_NestedLogitVariants_General_NestedPR
-- name    : NestedLogitVariants_General_NestedPR
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T21:26:40.059113+00:00
-- url     : https://prove2.me/theorems/40930199-1d7a-421a-ae48-9b956d6fb4ba
-- title:
--   pp. 24–26 — the assortments N^k_ij and the candidate collection {N^k_ij} ∪ {{j}} of Theorem 11
-- statement:
--   Fix a nest $i$ and an integer $k\in\{0,\dots,n\}$. Among the products of nest $i$, take the $k$ products with the smallest preference weights; among those, $N^k_{ij}$ is the nested-by-revenue assortment that keeps the first $j$ products with the largest revenues, for $j=0,\dots,k$, with $N^k_{i0}=\emptyset$ (pp. 24–25).
--
--   The candidate collection of nest $i$ used in Theorem 11 is
--   $$
--   \{N^k_{ij} : k\in N,\ j=0,\dots,k\}\ \cup\ \{\{j\} : j\in N\},
--   $$
--   which contains at most $1+n+n^2$ assortments (p. 26). For $k=n$ every product is kept, so $N^n_{ij}$ is the nested-by-revenue assortment $N_{ij}$.
--
--   **Formalization Note** Ties are broken by index: "the $k$ smallest preference weights" means the $k$ smallest pairs $(v_{il},l)$ in lexicographic order (`weightLt`, `smallK`), and "the first $j$ products with the largest revenues" means the $j$ smallest indices, which is revenue order because $r_{i1}\ge\dots\ge r_{in}$. In `candidatesPR`, $k$ ranges over $1,\dots,n$ and $j$ over $0,\dots,k$, as on the page.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), pp. 24–25, definition of N^k_ij; p. 26, Theorem 11 (the collection)

import Mathlib
import Definitions.Def_NestedLogitVariants_General_Model

namespace NestedLogitVariants.General

open Classical

variable {ι : Type*} {n : ℕ}

/-- `(v_il, l)` precedes `(v_ij, j)` lexicographically. -/
def weightLt (I : Instance ι n) (i : ι) (l j : Fin n) : Prop :=
  I.v i l < I.v i j ∨ (I.v i l = I.v i j ∧ l < j)

/-- The products with the `k` smallest preference weights in nest `i`. -/
noncomputable def smallK (I : Instance ι n) (i : ι) (k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => (Finset.univ.filter (fun l => weightLt I i l j)).card < k)

/-- `N^k_ij`: the first `j` products (index = revenue order) among `smallK I i k`. -/
noncomputable def nestedPR (I : Instance ι n) (i : ι) (k j : ℕ) : Finset (Fin n) :=
  (smallK I i k).filter (fun l => ((smallK I i k).filter (fun l' => l' < l)).card < j)

/-- The candidate collection of nest `i` used in Theorem 11 (pp. 25–26):
`{N^k_ij : k ∈ N, j = 0, …, k} ∪ {{j} : j ∈ N}`, with `k` ranging over `1, …, n` and
`N^k_i0 = ∅`. -/
def candidatesPR (I : Instance ι n) (i : ι) : Set (Finset (Fin n)) :=
  {S | (∃ k ∈ Finset.Icc 1 n, ∃ j ≤ k, S = nestedPR I i k j) ∨ ∃ j, S = {j}}

end NestedLogitVariants.General


