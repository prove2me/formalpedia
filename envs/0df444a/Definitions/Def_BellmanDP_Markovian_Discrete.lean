-- Prove2me | Definitions.Def_BellmanDP_Markovian_Discrete
-- name    : BellmanDP_Markovian_Discrete
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T21:35:12.582821+00:00
-- url     : https://prove2.me/theorems/3c5093d8-143e-4ebf-a0de-a47eecc8ab84
-- title:
--   The row-wise maximized positive matrix family $A(q)$, its Perron root $\varphi(q)$, and the recurrence $x(n+1)=\max_q A(q)x(n)$
-- statement:
--   This file sets up the discrete Markovian decision process of Chapter XI, § 10.
--
--   Fix $N \ge 1$. Row $i$ of the matrix carries its own parameter $q_i$, ranging over a set $S_i$; the joint parameter is $q = (q_1, \dots, q_N)$, ranging over the product $S = S_1 \times \dots \times S_N$. Row $i$ of the matrix $A(q) = (a_{ij}(q))$ depends only on $q_i$: $a_{ij}(q) = a_{ij}(q_i)$. This is Bellman's convention that "the maximum is taken element by element", with "no interaction between the various maximizations" (§ 3).
--
--   1. The matrix $A(q)$ for a joint parameter $q$.
--   2. The **Perron root** $\varphi(q)$: the characteristic root of $A(q)$ of largest absolute value, that is,
--   $$\varphi(q) = \max\{\, |\mu| : \mu \in \mathbb C,\ \det(\mu I - A(q)) = 0 \,\}.$$
--   3. The homogeneous system (10.2): a pair $(\lambda, y)$ solves it when, for every $i$,
--   $$\lambda y_i = \max_{q_i \in S_i} \sum_{j=1}^N a_{ij}(q_i)\, y_j ,$$
--   the maximum being attained.
--   4. The conditions (10.3): (a) for every vector $y \in \mathbb R^N$ and every row $i$ the maximum of $\sum_j a_{ij}(q_i) y_j$ over $q_i \in S_i$ is attained; (b) $0 < a_{ij}(q) \le m < \infty$ for $q \in S$; (c) $\varphi$ attains its maximum on $S$.
--   5. The recurrence (10.1): $x_i(0) = c_i$ and
--   $$x_i(n+1) = \max_{q_i \in S_i} \sum_{j=1}^N a_{ij}(q_i)\, x_j(n), \qquad n \ge 0 .$$
--
--   These objects are shared by Theorems 2 and 3 of the chapter.
--
--   **Formalization Note** The Perron root is the spectral radius of $A(q)$ viewed as a complex matrix (`spectralRadius ℂ`), converted to a real number; it is not defined as "the positive eigenvalue with a positive eigenvector", so the Perron–Frobenius content of Theorem 2 is not built into the definition. The maximum in the recurrence is written as a real supremum over $S_i$, which is the book's maximum under condition (a).
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter XI, § 3, Eqs. (3.1), (3.4), pp. 319-320; § 10, Eqs. (10.1)-(10.3), pp. 328-329

import Mathlib

namespace BellmanDP.Markovian

open Finset

/-- Bellman, *Dynamic Programming*, Ch. XI, § 3, (3.1) and (3.4), pp. 319–320: the matrix
`A(q) = (a_ij(q))` of a row-wise parametrized family. Row `i` carries its own parameter
`q_i : Q i` ("the set of q's for each row is distinct from the corresponding set for any other
row"), and `q = (q₁, …, q_N)` is the joint parameter. -/
def matOf {N : ℕ} {Q : Fin N → Type*} (a : (i : Fin N) → Q i → Fin N → ℝ)
    (q : (i : Fin N) → Q i) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => a i (q i) j

/-- Ch. XI, § 10, condition (3c), p. 329: the Perron root `φ(q)` of `A(q)`, "the characteristic
root of `A(q)` of largest absolute value". It is the spectral radius of the matrix regarded as a
complex matrix, i.e. the largest modulus of a complex eigenvalue (finite, since the spectrum of a
square matrix is finite). -/
noncomputable def perronRoot {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  (spectralRadius ℂ (A.map (algebraMap ℝ ℂ))).toReal

/-- Ch. XI, § 10, Eq. (10.2), p. 329: `(λ, y)` solves the homogeneous system
`λ y_i = Max_q Σ_{j=1}^N a_ij(q) y_j`, `i = 1, …, N`, the maximum over row `i`'s parameter set
`S i` being attained and equal to `λ y_i`. -/
def IsMaxEigenpair {N : ℕ} {Q : Fin N → Type*} (a : (i : Fin N) → Q i → Fin N → ℝ)
    (S : (i : Fin N) → Set (Q i)) (lam : ℝ) (y : Fin N → ℝ) : Prop :=
  ∀ i : Fin N, IsGreatest ((fun q => ∑ j, a i q j * y j) '' S i) (lam * y i)

/-- Ch. XI, § 10, conditions (3a)–(3c), p. 329, for the row-wise family `a` with row parameter
sets `S i` (the joint parameter set is the product `Set.pi Set.univ S`) and bound `m`. -/
structure MarkovHyp {N : ℕ} {Q : Fin N → Type*} (a : (i : Fin N) → Q i → Fin N → ℝ)
    (S : (i : Fin N) → Set (Q i)) (m : ℝ) : Prop where
  /-- (3a) for any `(y₁, …, y_N)` the maximum in (10.1) is attained, row by row. -/
  attain : ∀ (y : Fin N → ℝ) (i : Fin N), ∃ q ∈ S i, ∀ q' ∈ S i,
    ∑ j, a i q' j * y j ≤ ∑ j, a i q j * y j
  /-- (3b) `0 < a_ij(q)` for `q ∈ S`. -/
  pos : ∀ (i : Fin N), ∀ q ∈ S i, ∀ j : Fin N, 0 < a i q j
  /-- (3b) `a_ij(q) ≤ m < ∞` for `q ∈ S`. -/
  bdd : ∀ (i : Fin N), ∀ q ∈ S i, ∀ j : Fin N, a i q j ≤ m
  /-- (3c) the Perron root `φ(q)` assumes its maximum for `q ∈ S`. -/
  perron_max : ∃ qs ∈ Set.pi Set.univ S, ∀ q ∈ Set.pi Set.univ S,
    perronRoot (matOf a q) ≤ perronRoot (matOf a qs)

/-- Ch. XI, § 10, Eq. (10.1), p. 328: the sequence `x_i(0) = c_i`,
`x_i(n + 1) = Max_q Σ_{j=1}^N a_ij(q) x_j(n)`. The maximum is written as the real supremum of
row `i`'s values over `S i`; under (3a) the supremum is attained, so it is the book's maximum. -/
noncomputable def maxIter {N : ℕ} {Q : Fin N → Type*} (a : (i : Fin N) → Q i → Fin N → ℝ)
    (S : (i : Fin N) → Set (Q i)) (c : Fin N → ℝ) : ℕ → Fin N → ℝ
  | 0 => c
  | n + 1 => fun i => sSup ((fun q => ∑ j, a i q j * maxIter a S c n j) '' S i)

end BellmanDP.Markovian


