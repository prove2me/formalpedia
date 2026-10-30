-- Prove2me | Definitions.Def_NestedLogitAssort_General_IsWeightOrder
-- name    : NestedLogitAssort_General_IsWeightOrder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:43:31.15814+00:00
-- url     : https://prove2.me/theorems/ab4987cb-3928-4128-beec-cd0b27085617
-- title:
--   Listing of a nest's products by nondecreasing preference weight
-- statement:
--   A permutation $\sigma$ of $N$ is a weight order for nest $i$ when
--
--   $$
--   v_{i\sigma(1)}\le v_{i\sigma(2)}\le\dots\le v_{i\sigma(n)} .
--   $$
--
--   Then $\{\sigma(1),\dots,\sigma(k)\}$ is a set of $k$ products with the smallest preference weights in nest $i$, the set from which the paper builds the assortments $N^k_{ij}$.
--
--   **Formalization Note** When weights are tied the $k$ lightest products are not unique; the theorems of this mission quantify over every weight order.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, Section 5, p. 25

import Mathlib
import Definitions.Def_NestedLogitAssort_General_Instance

namespace NestedLogitAssort.General

/-- **A listing of the products of a nest by nondecreasing preference weight.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, Section 5, p. 25 (unnumbered): "the products with the `k` smallest preference weights".

`IsWeightOrder I i σ` says that `σ 0, σ 1, …, σ (n − 1)` lists the products of nest `i` in order of
nondecreasing weight `v_{ij}`, so that `{σ 0, …, σ (k − 1)}` are `k` products with the smallest
weights.

**Formalization Note.** When weights are tied, the `k` products with the smallest weights are not
unique; the theorems of this mission quantify over every such listing `σ`. -/
def IsWeightOrder {M : Type*} {n : ℕ} (I : Instance M n) (i : M) (σ : Equiv.Perm (Fin n)) :
    Prop :=
  Monotone (fun a => I.v i (σ a))

end NestedLogitAssort.General


