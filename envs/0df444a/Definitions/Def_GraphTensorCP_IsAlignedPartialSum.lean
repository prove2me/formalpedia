-- Prove2me | Definitions.Def_GraphTensorCP_IsAlignedPartialSum
-- name    : GraphTensorCP_IsAlignedPartialSum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:04:11.909918+00:00
-- url     : https://prove2.me/theorems/46372688-c9f4-4dc9-9378-4ee2adff2eae
-- title:
--   Aligned partial direct sum $A=A_1\boxplus_e\cdots\boxplus_e A_s$, $e=(k-1,k)$
-- statement:
--   Let $k\ge2$ and $s\ge1$, and let $e=(k-1,k)$ be the last two legs. Tensors $A_1,\dots,A_s$ of order $k$ that have the same dimensions on the first $k-2$ legs can be combined into the **partial direct sum in aligned coordinates** $A=A_1\boxplus_e\cdots\boxplus_e A_s$: on each of the two legs $k-1,k$ the blocks occupy disjoint coordinate sectors (as in a direct sum), while on the first $k-2$ legs they use one common, identified coordinate system. All entries outside the blocks are zero.
--
--   In the formalization, $A$ is an aligned partial sum of $A_1,\dots,A_s$ when there are linear maps $f_{h,d}$ from leg $d$ of $A_h$ to leg $d$ of $A$ such that
--
--   1. on every shared leg $d\le k-2$, each $f_{h,d}$ is bijective;
--   2. on each of the legs $k-1,k$, each $f_{h,d}$ is injective and the images of the different blocks are independent subspaces;
--   3. $A=\sum_h(\bigotimes_d f_{h,d})(A_h)$.
--
--   This is the structure produced by the separation and degeneration constructions of Sections 3–4, and the input of the entropy inequality (Corollary 3.5).
--
--   **Formalization Note** The paper defines $\boxplus_e$ by a coordinate formula; the predicate is more general: the paper's partial sum satisfies it with the sector inclusions and the identity on the shared legs, and every instance is a paper partial sum of blocks isomorphic to the $A_h$, padded with zero coordinates on the last two legs. Bijectivity on the shared legs is essential: it forces a common coordinate system there. Legs are 0-based, so $e$ is the pair of indices $k-2,k-1$.
-- source:
--   H. Zhou, Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers, arXiv:2610.34273 (version of 2026-11-03), Definition 2.9, pp.16–17

import Mathlib
import Definitions.Def_mme_tensor

universe u

namespace GraphTensorCP

/-- **Partial direct sum in aligned coordinates** `A = A₁ ⊞_e ⋯ ⊞_e A_s` with `e = (k−1, k)`
(Zhou, *Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers*,
arXiv:2610.34273 (version of 2026-11-03), Definition 2.9, pp.16–17): the blocks share the
coordinates of the first `k − 2` legs ("identify these coordinates in the displayed order") and
occupy disjoint coordinate sectors on the last two legs, and `A` is the sum of the blocks placed
in these sectors.

`IsAlignedPartialSum A B` holds when there are linear maps `f h d : (B h).V d → A.V d` with
1. `f h d` **bijective** on every shared leg `d < k − 2` (0-based), for every block `h`;
2. on each of the two legs `k − 2, k − 1` (the paper's `k − 1, k`), every `f h d` injective and
   the ranges of the blocks independent (disjoint sectors);
3. `A = Σ_h (⊗_d f h d)(B h)`.

**Formalization Note.** This is a predicate on tensor objects instead of the paper's
coordinate formula, and it is more general: the paper's partial sum satisfies it with the
sector inclusions and the identity on shared legs, while any instance is a paper partial sum of
the blocks transported through `f h d` (locally isomorphic to the `B h`), padded by zero
coordinates on the last two legs; neither change affects a spectral value. Bijectivity on the
shared legs is essential: it is what forces one common coordinate system on those legs. -/
def IsAlignedPartialSum {K : Type u} [Field K] {k s : ℕ} (A : MME.TensorObj K k)
    (B : Fin s → MME.TensorObj K k) : Prop :=
  ∃ f : ∀ h d, (B h).V d →ₗ[K] A.V d,
    (∀ h d, d.val < k - 2 → Function.Bijective (f h d)) ∧
    (∀ d, k - 2 ≤ d.val →
      (∀ h, Function.Injective (f h d)) ∧ iSupIndep (fun h => LinearMap.range (f h d))) ∧
    A.t = ∑ h, PiTensorProduct.map (f h) (B h).t

end GraphTensorCP


