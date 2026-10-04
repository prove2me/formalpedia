-- Prove2me | Definitions.Def_ShadowTomography_UpperBound_tensorPow
-- name    : ShadowTomography_UpperBound_tensorPow
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T01:41:05.205551+00:00
-- url     : https://prove2.me/theorems/1700cd1a-8d13-4541-bdea-d387f55e3a4c
-- title:
--   Tensor power $\rho^{\otimes k}$ of a matrix, indexed by k-tuples of basis labels
-- statement:
--   For a matrix $\rho$ on a system with basis labels $n$ and a natural number $k$, the **$k$-fold tensor power** $\rho^{\otimes k}$ is the matrix on $k$ registers whose basis labels are $k$-tuples $x=(x_1,\dots,x_k)$, with entries
--
--   $$
--   \rho^{\otimes k}_{x,y} = \prod_{j=1}^{k} \rho_{x_j, y_j}.
--   $$
--
--   If $\rho$ is a mixed state, $\rho^{\otimes k}$ is the joint state of $k$ independent copies of $\rho$. For $k=0$ it is the $1\times 1$ matrix $(1)$, the state of the empty system. Shadow tomography asks how large $k$ must be for a measurement of $\rho^{\otimes k}$ to estimate many acceptance probabilities of $\rho$ at once.
--
--   **Formalization Note** The index type is `Fin k → n` for every $k$, rather than an iterated Kronecker product, so that statements of the form "there exists $k$ such that a measurement of $\rho^{\otimes k}$ ..." typecheck uniformly in $k$.
-- source:
--   Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2, p. 2, Problem 1 (ρ^{⊗k})

import Mathlib

namespace ShadowTomography.UpperBound

/-- The `k`-fold tensor power `ρ^{⊗k}` of a matrix `ρ : Matrix n n ℂ`, indexed by `k`-tuples
`x : Fin k → n` of basis labels: its `(x, y)` entry is `∏ j, ρ (x j) (y j)`.
At `k = 0` it is the `1 × 1` matrix `1`. -/
def tensorPow {n : Type} (ρ : Matrix n n ℂ) (k : ℕ) : Matrix (Fin k → n) (Fin k → n) ℂ :=
  fun x y => ∏ j, ρ (x j) (y j)

end ShadowTomography.UpperBound


