-- Prove2me | Definitions.Def_RandTreeUniv_StepPasses
-- name    : RandTreeUniv_StepPasses
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:10:22.36419+00:00
-- url     : https://prove2.me/theorems/0339d3ed-8ce0-4080-a9dd-7b90c490e3f2
-- title:
--   A step of the leaf-cutting Algorithm 6.5
-- statement:
--   Algorithm 6.5 takes a tree with one or more roots, sets $\hat T\leftarrow T$, and repeatedly removes the set $D_i$ of leaves of $\hat T$ (degree-one vertices of $\hat T$ other than the roots). **Step $i$ passes** with threshold $a$ if
--
--   $$
--   D_i\ \text{contains a 24-separated set of at least } a \text{ vertices, all at distance at least 2 from the roots,}
--   $$
--
--   where a set is $24$-separated if any two of its vertices are at distance at least $24$ (Definition 2.12). In §6 the threshold is $a=(10+\delta_1)\alpha$. The algorithm rejects at the first step that fails and stops successfully after step $\Gamma+1$.
--
--   **Formalization Note** The module defines `leafSet` (the leaves of $\hat T$, roots discarded), `remSet` (the vertex set of $\hat T$ after $i$ removals) and `StepPasses`, whose step index is 0-based: `StepPasses … i` tests $D_{i+1}$. Distances are taken in the whole tree, which agrees with distances inside the subtree being processed. "Of size $(10+\delta_1)\alpha$" is read as "of size at least $(10+\delta_1)\alpha$".
-- source:
--   A. Cohen Antonir, L. Lichev, M. Zhukovskii, Universality in random graphs via optimal linking systems: trees and beyond, arXiv:2608.06358 (held revision, sha256 33e85b21…69a55921), §6, Algorithm 6.5, pp.31–32 (PDF 32–33); Definition 2.12, p.12 (PDF 13)

import Mathlib

set_option autoImplicit false

open scoped Classical

namespace RandTreeUniv

/-- The leaves of the rooted tree `T̂ = T[R]` (Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), §6, p.31 (PDF 32)): the vertices of `R` with
exactly one neighbour in `R`, discarding the roots ("the set of leaves of a rooted tree is obtained
from the set of leaves of its unrooted counterpart by discarding the roots"). -/
noncomputable def leafSet {V : Type*} [Fintype V] (T : SimpleGraph V) (roots R : Finset V) :
    Finset V :=
  R.filter fun v => v ∉ roots ∧ (R.filter fun u => T.Adj v u).card = 1

/-- The vertex set of `T̂` in Algorithm 6.5 (p.31 (PDF 32)) after `i` leaf-removal steps, starting
from the tree `T[W]` with the given roots: `remSet 0 = W`, `remSet (i+1) = remSet i \ D_{i+1}`. -/
noncomputable def remSet {V : Type*} [Fintype V] (T : SimpleGraph V) (roots W : Finset V) :
    ℕ → Finset V
  | 0 => W
  | i + 1 => remSet T roots W i \ leafSet T roots (remSet T roots W i)

/-- Step `i + 1` of Algorithm 6.5 (Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), p.31–32 (PDF 32–33)) is passed, with threshold
`a = (10 + δ₁)α`: the set `D_{i+1}` of leaves of `T̂` (after `i` removals) contains a
24-separated set (Definition 2.12, p.12) of at least `a` vertices, all at distance at least `2`
from the roots.

**Formalization Note** 0-based step index: `StepPasses … i` is the paper's test on `D_{i+1}`.
Distances are measured in the whole tree `T`; for vertices of a subtree `T[W]` of a tree they
equal the distances in `T[W]` (the unique path stays inside the subtree). "Of size `(10 + δ₁)α`"
is read as "of size at least `(10 + δ₁)α`" (a larger separated set contains one of each smaller
size). -/
def StepPasses {V : Type*} [Fintype V] (T : SimpleGraph V) (roots W : Finset V) (a : ℝ)
    (i : ℕ) : Prop :=
  ∃ X ⊆ leafSet T roots (remSet T roots W i), a ≤ (X.card : ℝ) ∧
    (∀ x ∈ X, ∀ y ∈ X, x ≠ y → 24 ≤ T.dist x y) ∧ ∀ x ∈ X, ∀ ρ ∈ roots, 2 ≤ T.dist x ρ

end RandTreeUniv


