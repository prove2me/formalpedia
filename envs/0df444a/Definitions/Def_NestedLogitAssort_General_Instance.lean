-- Prove2me | Definitions.Def_NestedLogitAssort_General_Instance
-- name    : NestedLogitAssort_General_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:38:10.158128+00:00
-- url     : https://prove2.me/theorems/93a0c2c3-ff28-4e73-8103-94d2b852fd9f
-- title:
--   Data of a nested logit assortment instance
-- statement:
--   An instance of the assortment problem under the nested logit model consists of
--
--   1. a finite set $M$ of nests and the product set $N=\{1,\dots,n\}$ of every nest;
--   2. the preference weight $v_0$ of the option of choosing no nest;
--   3. for every nest $i$, the preference weight $v_{i0}$ of the no-purchase option inside the nest;
--   4. for every nest $i$ and product $j$, the revenue $r_{ij}$ and the preference weight $v_{ij}$;
--   5. for every nest $i$, the dissimilarity parameter $\gamma_i$.
--
--   This record carries the data only; every assumption on it (signs, ordering of revenues, range of $\gamma_i$) is stated explicitly in the theorems that use it.
--
--   **Formalization Note** Products are indexed by `Fin n`, so index $0$ is the paper's product $1$.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, Section 1, pp. 6–7

import Mathlib

namespace NestedLogitAssort.General

/-- **Data of a nested logit assortment instance.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, Section 1, pp. 6–7 (unnumbered).

There are `m` nests, indexed by the finite type `M`, and `n` products in every nest, indexed by
`Fin n` (index `0` is the paper's product `1`). The fields are:

* `v0` — `v_0`, the preference weight of not choosing any nest (p. 7);
* `w0 i` — `v_{i0}`, the preference weight of the no-purchase option inside nest `i` (p. 7);
* `v i j` — `v_{ij}`, the preference weight of product `j` in nest `i` (p. 7);
* `r i j` — `r_{ij}`, the revenue of product `j` in nest `i` (p. 7);
* `γ i` — `γ_i`, the dissimilarity parameter of nest `i` (p. 7).

**Formalization Note.** The structure holds the data only. Every assumption of the paper
(nonnegative weights and revenues, `r_{i1} ≥ … ≥ r_{in}`, `γ_i ≥ 0`, `max_i γ_i > 1`) is an
explicit hypothesis of each theorem that uses it. -/
structure Instance (M : Type*) (n : ℕ) where
  /-- `v_0`: weight of the option of not choosing any nest. -/
  v0 : ℝ
  /-- `v_{i0}`: weight of the no-purchase option inside nest `i`. -/
  w0 : M → ℝ
  /-- `v_{ij}`: preference weight of product `j` in nest `i`. -/
  v : M → Fin n → ℝ
  /-- `r_{ij}`: revenue of product `j` in nest `i`. -/
  r : M → Fin n → ℝ
  /-- `γ_i`: dissimilarity parameter of nest `i`. -/
  γ : M → ℝ

end NestedLogitAssort.General


