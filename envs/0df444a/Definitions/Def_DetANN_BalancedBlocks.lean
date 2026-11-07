-- Prove2me | Definitions.Def_DetANN_BalancedBlocks
-- name    : DetANN_BalancedBlocks
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:25:42.463776+00:00
-- url     : https://prove2.me/theorems/2323a896-355e-4b4a-8c46-03d84cac8dca
-- title:
--   Balanced block systems (Definition 3.1)
-- statement:
--   Let $P\subseteq\mathbb R^d$ be finite, $\tau\in(0,1)$, and let $A_1,\dots,A_d:\mathbb R^d\to\mathbb R^b$ be linear maps. They form a **$\tau$-balanced block system for $P$** if
--
--   $$\sum_{i=1}^d\|A_iz\|_2^2=\|z\|_2^2\quad\text{for every }z\in\mathbb R^d\qquad(8)$$
--
--   and, for all $x,y\in P$ and every $i\in[d]$,
--
--   $$\frac{1-\tau}{d}\|x-y\|_2^2\le\|A_i(x-y)\|_2^2\le\frac{1+\tau}{d}\|x-y\|_2^2.\qquad(9)$$
--
--   The first property is the Parseval identity; the second asks each block to see every difference of database points with almost exactly its share $1/d$ of the squared length.
--
--   **Formalization Note** The condition $\tau\in(0,1)$ is assumed by every theorem that uses the predicate, not inside it.
-- source:
--   Feng, Indyk, Deterministic Approximate Nearest Neighbors in High Dimensions, STOC 2027 submission (manuscript sha256 96f0ad57b9d12ba3ac6f9e61c88ddfd6b621e077d7e2a9821906e5b4ff0d0e82), Definition 3.1, p.7

import Mathlib

namespace DetANN

/-!
# Balanced block systems

Y. Feng, P. Indyk, *Deterministic Approximate Nearest Neighbors in High Dimensions*, STOC 2027
submission (manuscript sha256 96f0ad57…), Definition 3.1, p.7.

**Formalization Note.** Points are elements of `EuclideanSpace ℝ (Fin d)` and blocks are linear
maps into `EuclideanSpace ℝ (Fin b)`; `‖·‖` is the Euclidean norm. The point set `P` is a `Finset`.
The paper's standing condition `τ ∈ (0, 1)` is not part of the predicate: every theorem that uses
it assumes `0 < τ` and `τ < 1` explicitly.
-/

/-- `A₁, …, A_d : ℝ^d → ℝ^b` form a `τ`-balanced block system for `P`:
(8) `∑ᵢ ‖Aᵢ z‖² = ‖z‖²` for every `z ∈ ℝ^d` (Parseval), and
(9) `(1 − τ)/d · ‖x − y‖² ≤ ‖Aᵢ(x − y)‖² ≤ (1 + τ)/d · ‖x − y‖²` for all `x, y ∈ P` and every `i`. -/
def IsBalancedBlockSystem {d b : ℕ} (τ : ℝ) (P : Finset (EuclideanSpace ℝ (Fin d)))
    (A : Fin d → EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin b)) : Prop :=
  (∀ z : EuclideanSpace ℝ (Fin d), ∑ i, ‖A i z‖ ^ 2 = ‖z‖ ^ 2) ∧
  ∀ x ∈ P, ∀ y ∈ P, ∀ i : Fin d,
    (1 - τ) / d * ‖x - y‖ ^ 2 ≤ ‖A i (x - y)‖ ^ 2 ∧
    ‖A i (x - y)‖ ^ 2 ≤ (1 + τ) / d * ‖x - y‖ ^ 2

end DetANN


