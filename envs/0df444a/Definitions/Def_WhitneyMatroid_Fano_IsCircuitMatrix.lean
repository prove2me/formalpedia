-- Prove2me | Definitions.Def_WhitneyMatroid_Fano_IsCircuitMatrix
-- name    : WhitneyMatroid_Fano_IsCircuitMatrix
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T04:49:20.119037+00:00
-- url     : https://prove2.me/theorems/a082c0c1-3cdb-4c96-b9a6-cab9e1aec693
-- title:
--   The sets $Z_{i_1\cdots i_p}$ and the circuit matrix of a matrix (§§14–15)
-- statement:
--   **The sets $Z_{i_1\cdots i_p}$ (§15).** A vector $(a_1,\dots,a_n)$ is in $Z_{i_1\cdots i_p}$ if
--
--   $$
--   a_j\neq 0 \ (j=i_1,\dots,i_p),\qquad a_j=0\ (j\neq i_1,\dots,i_p),
--   $$
--
--   that is, its set of nonzero coordinates is exactly $\{i_1,\dots,i_p\}$.
--
--   **Circuit matrix (§14).** Let $\mathbf M=(a_{ij})$ be an $m\times n$ matrix and $M$ its matroid. If the columns $C_{i_1},\dots,C_{i_p}$ form a circuit $P$, there are numbers $b_1,\dots,b_n$ with
--
--   $$
--   a_{i1}b_1+\cdots+a_{in}b_n=0\quad(i=1,\dots,m),\qquad (b_1,\dots,b_n)\in Z_{i_1\cdots i_p}. \qquad (14.1)
--   $$
--
--   Choosing one such row for each circuit $P_1,\dots,P_s$ of $M$ gives a matrix $\mathbf M'=(b_{kj})$ with one row per circuit, the **circuit matrix** of $\mathbf M$. A matrix $B$ is a circuit matrix of $\mathbf M$ (with respect to a given one-to-one correspondence between its rows and the circuits of $M$) if $M$ is the matroid of $\mathbf M$ and every row of $B$ satisfies (14.1) for its circuit.
--
--   **Formalization Note** The rows of a circuit matrix are determined only up to nonzero factors, so the circuit matrix is a predicate on $B$, not a function of $\mathbf M$. The correspondence between the row index type and the circuits of $M$ is an explicit bijection `row`. The matrix $\mathbf M$ times the vector $b$ is Mathlib's `mulVec`.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), pp. 526–527, §14, (14.1); p. 528, §15

import Mathlib
import Definitions.Def_WhitneyMatroid_Fano_IsMatroidOf

namespace WhitneyMatroid.Fano

/-- Whitney §15 (p. 528): the vector `(a_j)_{j ∈ ι}` is in `Z_{i₁⋯i_p}`, where `S = {i₁, …, i_p}`:
`a_j ≠ 0` for `j ∈ S` and `a_j = 0` for `j ∉ S`. -/
def InZ {K : Type*} [Field K] {ι : Type*} (a : ι → K) (S : Set ι) : Prop :=
  ∀ j, a j ≠ 0 ↔ j ∈ S

/-- Whitney §14, (14.1) (pp. 526–527): `B` is a circuit matrix of the matrix `A`, whose matroid
is `M`. The rows of `B` are indexed by `κ`, which `row` puts in one-to-one correspondence with the
circuits of `M`; the row `b = B k` belonging to the circuit `P = row k` satisfies
`a_{i1} b_1 + ⋯ + a_{in} b_n = 0` for every row `i` of `A`, and `b_j ≠ 0` exactly for `j ∈ P`.
Each row is determined only up to a nonzero factor, so this is a predicate on `B`. -/
def IsCircuitMatrix {K : Type*} [Field K] {ι : Type*} [Fintype ι] {m : ℕ} {κ : Type*}
    (M : Matroid ι) (A : Matrix (Fin m) ι K) (B : Matrix κ ι K)
    (row : κ ≃ {P : Set ι // M.IsCircuit P}) : Prop :=
  IsMatroidOf M A ∧ ∀ k : κ, A.mulVec (B k) = 0 ∧ InZ (B k) (row k : Set ι)

end WhitneyMatroid.Fano


