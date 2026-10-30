-- Prove2me | Definitions.Def_NestedLogitAssort_General_NBR
-- name    : NestedLogitAssort_General_NBR
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:43:01.267696+00:00
-- url     : https://prove2.me/theorems/d5eb6059-1dc2-4416-bffa-1026a04c5998
-- title:
--   Nested-by-revenue assortment $N_{ij}=\{1,\dots,j\}$
-- statement:
--   With the products of every nest indexed so that $r_{i1}\ge r_{i2}\ge\dots\ge r_{in}$, the nested-by-revenue assortment of size $j$ is
--
--   $$
--   N_{ij}=\{1,2,\dots,j\},\qquad N_{i0}=\emptyset .
--   $$
--
--   It consists of the $j$ products with the largest revenues and does not depend on the nest.
--
--   **Formalization Note** Products are `Fin n`, so $N_{ij}$ is the set of indices $0,\dots,j-1$; $j$ is the paper's 1-based count, and for $j\ge n$ the set is all of $N$.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, Section 2, pp. 13–14

import Mathlib

namespace NestedLogitAssort.General

/-- **The nested-by-revenue assortment `N_{ij} = {1, …, j}`.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, Section 2, pp. 13–14 (unnumbered): `N_{ij} = {1, 2, …, j}` and `N_{i0} = ∅`.

`NBR n j` is the set of the first `j` products (the products are indexed in order of
nonincreasing revenue, p. 7). It does not depend on the nest.

**Formalization Note.** Products are `Fin n`, so the paper's products `1, …, j` are the indices
`0, …, j − 1`; `j` is the paper's 1-based count. For `j ≥ n` the set is all of `N`. -/
def NBR (n j : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun l : Fin n => l.val < j)

end NestedLogitAssort.General


