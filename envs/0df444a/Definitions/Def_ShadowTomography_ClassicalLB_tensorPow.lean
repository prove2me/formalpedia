-- Prove2me | Definitions.Def_ShadowTomography_ClassicalLB_tensorPow
-- name    : ShadowTomography_ClassicalLB_tensorPow
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T17:07:17.55965+00:00
-- url     : https://prove2.me/theorems/eb4fa822-d1b0-44f6-b1ce-4046fdb29d0e
-- title:
--   Tensor power of a quantum state
-- statement:
--   For a matrix $\rho$ indexed by a finite basis and a nonnegative integer $k$, the **tensor power** $\rho^{\otimes k}$ is the matrix indexed by strings $x,y$ of length $k$ with entries
--
--   $$
--   (\rho^{\otimes k})_{x,y}=\prod_{t=1}^{k}\rho_{x_t,y_t}.
--   $$
--
--   It represents $k$ independently prepared copies of the same state. At $k=0$, the index set has one empty string and the empty product is one.
-- source:
--   Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2, p. 2, Problem 1 (ρ^{⊗k})

import Mathlib

namespace ShadowTomography.ClassicalLB

/-- Matrix entries of `k` independent copies in the tensor-product basis. -/
def tensorPow {n : Type} [Fintype n] (ρ : Matrix n n ℂ) (k : ℕ) :
    Matrix (Fin k → n) (Fin k → n) ℂ :=
  fun x y => ∏ j : Fin k, ρ (x j) (y j)

end ShadowTomography.ClassicalLB


