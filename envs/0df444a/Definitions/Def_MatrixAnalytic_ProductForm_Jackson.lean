-- Prove2me | Definitions.Def_MatrixAnalytic_ProductForm_Jackson
-- name    : MatrixAnalytic_ProductForm_Jackson
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:48:04.376364+00:00
-- url     : https://prove2.me/theorems/c316af4e-6308-468c-aba7-b341bbe20359
-- title:
--   The Jackson network as a QBD: blocks (15.7)ff. and B = A₁ + μ₁I
-- statement:
--   A **Jackson network** has $K$ single-server nodes with infinite buffers. Services at node $i$ are exponential with rate $\mu_i$; external arrivals to node $i$ form a Poisson process of rate $\lambda_i$; a customer who completes its service at node $i$ moves to node $j$ with probability $P_{ij}$ and leaves the network with probability $q_i$.
--
--   The network is a QBD whose level is the number $n_1$ of customers at node $1$ and whose phase is the vector $\boldsymbol r=(n_2,\dots,n_K)\in\mathbb N^{K-1}$ of the numbers of customers at the other nodes. With $\boldsymbol e_j$ the unit vector of node $j$, and rates to $\boldsymbol r-\boldsymbol e_j$ present only when $n_j\ge 1$, the blocks are, for $2\le i,j\le K$:
--   $$A_0(\boldsymbol r,\boldsymbol r)=\lambda_1,\qquad A_0(\boldsymbol r,\boldsymbol r-\boldsymbol e_j)=\mu_jP_{j1},$$
--   $$A_2(\boldsymbol r,\boldsymbol r)=\mu_1q_1,\qquad A_2(\boldsymbol r,\boldsymbol r+\boldsymbol e_j)=\mu_1P_{1j},$$
--   $$A_1(\boldsymbol r,\boldsymbol r+\boldsymbol e_i)=\lambda_i,\qquad A_1(\boldsymbol r,\boldsymbol r-\boldsymbol e_j)=\mu_jq_j,\qquad A_1(\boldsymbol r,\boldsymbol r-\boldsymbol e_j+\boldsymbol e_i)=\mu_jP_{ji}\ (i\ne j),$$
--   $$A_1(\boldsymbol r,\boldsymbol r)=-\Big(\lambda_1+\mu_1+\sum_{2\le i\le K}\lambda_i+\sum_{2\le j\le K,\ n_j\ge 1}\mu_j\Big),$$
--   all other entries $0$, and $B=A_1+\mu_1 I$ (at level $0$ node $1$ is empty and does not serve).
--
--   **Formalization Note** The nodes are indexed by `Option J` with `J` a finite type: `none` is node $1$ and `some j` are nodes $2,\dots,K$, so $K=|J|+1$ and the phase is a function `J → ℕ`; $\lambda$ is written `lam`. The diagonal of $A_1$ is not displayed in the book's list of rates on p. 299; it is minus the total rate out of a state with $n_1\ge 1$, so that the rows of the generator sum to zero. The book's alternative form (15.11) of that diagonal, $A_1(\boldsymbol r,\boldsymbol r)=F(\boldsymbol r,\boldsymbol r)-\lambda_1+\mu_1$, has a sign error (it should read $-\mu_1$; finding F1) and is not used.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, pp. 295–296 (Section 15.1, the network) and pp. 299–300 (Section 15.2, Eq. (15.7) and the blocks A₂, A₁, B = A₁ + μ₁I)

import Mathlib

namespace MatrixAnalytic.ProductForm

noncomputable section

/-!
The Jackson network of §15.2 (pp. 299–300) of Latouche & Ramaswami written as a QBD. There are
`K` single-server nodes; here they are indexed by `Option J` with `J` a finite type, `none`
being the book's node `1` and `some j` the nodes `2, …, K` (so `K = card J + 1`). Node `i` has
exponential services of rate `μ_i`, external Poisson arrivals of rate `λ_i`; a customer leaving
node `i` moves to node `j` with probability `P_{ij}` and leaves the network with probability
`q_i`. The level is the number `n₁` of customers at node `1`; the phase is the vector
`r = (n₂, …, n_K)`, a function `J → ℕ`; `e_j` is `Pi.single j 1`.

The blocks are those of (15.7) and the two displays that follow it (p. 299), with `B = A₁ + μ₁I`
(p. 300). A rate `(15.7)` to `r − e_j` exists only if `n_j ≥ 1` ("we restrict the transitions to
feasible states"). The diagonal of `A₁` is minus the total rate out of a state with `n₁ ≥ 1`, so
that the rows of the generator sum to zero.
-/

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- `A₀` of (15.7): `A₀(r, r) = λ₁` (an arrival at node `1`) and
`A₀(r, r − e_j) = μ_j P_{j1}` for `n_j ≥ 1` (a customer moves from node `j` to node `1`). -/
def jacksonA₀ (lam μ : Option J → ℝ) (P : Option J → Option J → ℝ) :
    (J → ℕ) → (J → ℕ) → ℝ :=
  fun r s => (if s = r then lam none else 0) +
    ∑ j : J, (if 1 ≤ r j ∧ s = r - Pi.single j 1 then μ (some j) * P (some j) none else 0)

/-- `A₂` (p. 299): `A₂(r, r) = μ₁ q₁` (a customer leaves the network from node `1`) and
`A₂(r, r + e_j) = μ₁ P_{1j}` (a customer moves from node `1` to node `j`). -/
def jacksonA₂ (μ q : Option J → ℝ) (P : Option J → Option J → ℝ) :
    (J → ℕ) → (J → ℕ) → ℝ :=
  fun r s => (if s = r then μ none * q none else 0) +
    ∑ j : J, (if s = r + Pi.single j 1 then μ none * P none (some j) else 0)

/-- `A₁` (pp. 299–300): `A₁(r, r + e_i) = λ_i`, `A₁(r, r − e_j) = μ_j q_j` and
`A₁(r, r − e_j + e_i) = μ_j P_{ji}` (`i ≠ j`), for `n_j ≥ 1`, with diagonal
`A₁(r, r) = −(λ₁ + μ₁ + Σ_i λ_i + Σ_{j : n_j ≥ 1} μ_j)`. -/
def jacksonA₁ (lam μ q : Option J → ℝ) (P : Option J → Option J → ℝ) :
    (J → ℕ) → (J → ℕ) → ℝ :=
  fun r s =>
    (∑ i : J, (if s = r + Pi.single i 1 then lam (some i) else 0)) +
    (∑ j : J, (if 1 ≤ r j ∧ s = r - Pi.single j 1 then μ (some j) * q (some j) else 0)) +
    (∑ j : J, ∑ i : J,
      (if i ≠ j ∧ 1 ≤ r j ∧ s = r - Pi.single j 1 + Pi.single i 1
        then μ (some j) * P (some j) (some i) else 0)) +
    (if s = r then
      -(lam none + μ none + ∑ i : J, lam (some i) +
          ∑ j : J, (if 1 ≤ r j then μ (some j) else 0))
      else 0)

/-- `B = A₁ + μ₁ I` (p. 300): at level `0` node `1` is empty and does not serve. -/
def jacksonB (lam μ q : Option J → ℝ) (P : Option J → Option J → ℝ) :
    (J → ℕ) → (J → ℕ) → ℝ :=
  fun r s => jacksonA₁ lam μ q P r s + (if s = r then μ none else 0)

end

end MatrixAnalytic.ProductForm


