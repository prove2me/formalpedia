-- Prove2me | Definitions.Def_ContinualCounting_prefixSum
-- name    : ContinualCounting_prefixSum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:40:59.126195+00:00
-- url     : https://prove2.me/theorems/24333e5a-128b-4949-b72d-0baaf96ddf40
-- title:
--   The prefix-sum matrix $A$
-- statement:
--   The prefix-sum matrix $A$ is the $n\times n$ lower triangular matrix of all ones, so that
--   $$(Ay)_i=\sum_{j\le i}y_j\qquad(y\in\mathbb R^n).$$
--   A binary input $x\in\{0,1\}^n$ is viewed as a real vector, and $Ax$ is the vector of its $n$ running counts, the quantity a continual counting mechanism must release.
--
--   **Formalization Note** The map $y\mapsto Ay$ on `Fin n → ℝ`, with $0$-based coordinates; `bitVec` is the embedding of `Fin n → Bool`.
-- source:
--   Bairaktari, Dahl, Larsen, The Binary Tree Mechanism is Optimal for Differentially Private Continual Counting, arXiv:2607.00876 (sha256 986e6426…), §1, p.1 (PDF p.2)

import Mathlib

set_option autoImplicit false

namespace ContinualCounting

/-- The binary vector `x ∈ {0, 1}^n` as a real vector. -/
def bitVec {n : ℕ} (x : Fin n → Bool) : Fin n → ℝ := fun i => if x i then 1 else 0

/-- **The prefix-sum matrix `A`.** Bairaktari, Dahl, Larsen, arXiv:2607.00876 (sha256 986e6426…), p.1:
"A is the n×n lower triangular matrix of all ones, known as the prefix-sum matrix, with
(Ax)_i = ∑_{j≤i} x_j". This is the map `y ↦ Ay` on `ℝ^n`, with `0`-based coordinates `Fin n`. -/
def prefixSum {n : ℕ} (y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ j ∈ Finset.univ.filter (· ≤ i), y j

end ContinualCounting


