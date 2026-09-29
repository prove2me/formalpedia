-- Prove2me | Definitions.Def_RelaxationMethod_FullDim_FejerMonotone
-- name    : RelaxationMethod_FullDim_FejerMonotone
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:24:46.465303+00:00
-- url     : https://prove2.me/theorems/cb34acf2-6dcd-40a0-bec4-8e34762be624
-- title:
--   Point-wise closer (1.1) and Fejér-monotone sequences (2.1)–(2.2)
-- statement:
--   Let $A$ be a set of points in the Euclidean space $E_n$.
--
--   1. A point $p_1$ is **point-wise closer** than $p$ to $A$ if
--   $$
--   |p - a| > |p_1 - a| \qquad \text{for every } a \in A .
--   $$
--   2. An infinite sequence $q_0, q_1, q_2, \dots$ of points outside $A$ is **Fejér-monotone** with respect to $A$ if, for all $i = 0, 1, \dots$,
--   $$
--   q_i \ne q_{i+1}, \qquad |q_i - a| \ge |q_{i+1} - a| \quad \text{for all } a \in A .
--   $$
--
--   The inequality in the second condition is not strict. Fejér-monotonicity is the property of the relaxation sequence that Motzkin and Schoenberg use to prove its convergence (Lemma 1).
--
--   **Formalization Note** The space is `EuclideanSpace ℝ (Fin n)` and $|x - y|$ is `dist x y`. The set $A$ is arbitrary in both definitions; the paper introduces them for the polytope of the linear system.
-- source:
--   Motzkin and Schoenberg, The relaxation method for linear inequalities, Canad. J. Math. 6 (1954), p. 393, (1.1), and p. 397, (2.1)–(2.2)

import Mathlib

namespace RelaxationMethod.FullDim

/-- (1.1): `p₁` is point-wise closer than `p` to the set `A`, i.e. `|p - a| > |p₁ - a|` for
every `a ∈ A`. -/
def IsPointwiseCloser {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (p p₁ : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ x ∈ A, dist p₁ x < dist p x

/-- (2.1)–(2.2): the infinite sequence `q₀, q₁, …` of points outside `A` is Fejér-monotone with
respect to `A`: consecutive terms differ, and `|q_i - a| ≥ |q_{i+1} - a|` for all `a ∈ A`
and all `i` (non-strict). -/
def IsFejerMonotone {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (q : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  (∀ ν : ℕ, q ν ∉ A) ∧ (∀ ν : ℕ, q ν ≠ q (ν + 1)) ∧
    ∀ x ∈ A, ∀ ν : ℕ, dist (q (ν + 1)) x ≤ dist (q ν) x

end RelaxationMethod.FullDim


