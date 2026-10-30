-- Prove2me | Definitions.Def_KingDiagonal_alpha
-- name    : KingDiagonal_alpha
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:16.278047+00:00
-- url     : https://prove2.me/theorems/c19fedbb-5cee-41c9-91b0-e7ce140ccf9f
-- title:
--   Block traces $\alpha_i = \mathrm{Tr}(\rho)_{ii}$ (eq. 10)
-- statement:
--   Let $\rho$ be a matrix on $\mathbb C^n \otimes \mathbb C^k$, viewed as an $n\times n$ block matrix whose blocks $(\rho)_{ij}$ are $k\times k$ matrices. For each $i$, define
--
--   $$
--   \alpha_i = \operatorname{Tr}(\rho)_{ii} = \sum_{a} \rho_{(i,a),(i,a)} .
--   $$
--
--   For a state $\rho$ the diagonal blocks are positive semidefinite, so $\alpha_i \ge 0$ and $\sum_i \alpha_i = \operatorname{Tr}\rho = 1$. These weights are the first step of King's decomposition of $\rho$ as a Hadamard product.
--
--   **Formalization Note** Matrices on $\mathbb C^{kn}$ are indexed by pairs $(i,a) \in n \times k$, block index first. $\alpha_i$ is returned as the real part of the block trace (real for a state).
-- source:
--   King, An application of a matrix inequality in quantum information theory, arXiv:quant-ph/0412046v1, eq. (10), p.4

import Mathlib

namespace KingDiagonal

/-- King, arXiv:quant-ph/0412046v1, eq. (10), p.4: for a matrix `ρ` on `C^n ⊗ C^k`, viewed as
an `n × n` block matrix with `k × k` blocks `(ρ)_{ij}`, `α_i = Tr (ρ)_{ii}`.

**Formalization Note.** Matrices on `C^{kn}` are `Matrix (n × k) (n × k) ℂ` with the block index
first: the block `(ρ)_{ij}` is `fun a b => ρ (i, a) (j, b)`. `α_i` is returned as a real number,
the real part of the (for a state, real and nonnegative) trace of the `i`-th diagonal block. -/
noncomputable def alpha {n k : Type*} [Fintype k] (ρ : Matrix (n × k) (n × k) ℂ) (i : n) : ℝ :=
  (∑ a : k, ρ (i, a) (i, a)).re

end KingDiagonal


