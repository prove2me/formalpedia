-- Prove2me | Definitions.Def_NestedLogitAssort_General_NK
-- name    : NestedLogitAssort_General_NK
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:44:11.498918+00:00
-- url     : https://prove2.me/theorems/367a87b7-b5ad-4729-a9b4-4367f97c9572
-- title:
--   The assortment $N^k_{ij}$
-- statement:
--   Restrict attention to the $k$ products $L_\sigma(k)$ with the smallest preference weights. The assortment $N^k_{ij}$ is the nested-by-revenue assortment of these products of size $j$: the $j$ products of $L_\sigma(k)$ with the largest revenues, with $N^k_{i0}=\emptyset$.
--
--   For $k=n$ every product is included and $N^n_{ij}=N_{ij}$.
--
--   **Formalization Note** The products are indexed in order of nonincreasing revenue, so the $j$ products with the largest revenues are taken to be the $j$ smallest indices in $L_\sigma(k)$ (revenue ties broken by index). For $j\ge k$ the set is all of $L_\sigma(k)$.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, Section 5, p. 25 (and p. 26 for N^n_ij = N_ij)

import Mathlib
import Definitions.Def_NestedLogitAssort_General_Light

namespace NestedLogitAssort.General

/-- **The assortment `N^k_{ij}`.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, Section 5, p. 25 (unnumbered): "Given that we focus only on the products with the `k`
smallest preference weights, we use `N^k_{ij}` to denote the nested-by-revenue assortment that
includes the first `j` products with the largest revenues in nest `i`", with `N^k_{i0} = ∅`.

`NK σ k j` is the set of the `j` products of `Light σ k` with the smallest indices (all of
`Light σ k` when `j ≥ k`).

**Formalization Note.** Products are indexed in order of nonincreasing revenue (p. 7), so the `j`
smallest indices are `j` products with the largest revenues, revenue ties being broken by index.
With `k = n`, `Light σ n = N` and `NK σ n j = N_{ij}`, as the paper notes on p. 26. -/
def NK {n : ℕ} (σ : Equiv.Perm (Fin n)) (k j : ℕ) : Finset (Fin n) :=
  (Light σ k).filter (fun l => ((Light σ k).filter (· < l)).card < j)

end NestedLogitAssort.General


