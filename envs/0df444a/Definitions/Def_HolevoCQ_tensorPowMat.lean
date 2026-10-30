-- Prove2me | Definitions.Def_HolevoCQ_tensorPowMat
-- name    : HolevoCQ_tensorPowMat
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:25.733214+00:00
-- url     : https://prove2.me/theorems/ee7f9d68-68da-4f81-bce6-619536434621
-- title:
--   Tensor power $\bar S^{\otimes n}$ of an operator
-- statement:
--   Let $\mathcal H=\mathbb C^D$ for a finite set $D$ and let $\rho$ be an operator on $\mathcal H$. Its $n$-fold tensor power is the operator on $\mathcal H^{\otimes n}=\mathbb C^{D^n}$ with matrix entries
--
--   $$
--   (\rho^{\otimes n})_{(a_1,\dots,a_n),(b_1,\dots,b_n)}=\prod_{l=1}^n \rho_{a_l b_l}.
--   $$
--
--   In Holevo's paper it is applied to the average state $\bar S$, giving $\bar S^{\otimes n}$, the state whose typical subspace is used in the random-coding argument.
--
--   **Formalization Note** $\mathcal H^{\otimes n}$ is indexed by words `Fin n → D`; at $n=0$ this is the $1\times1$ identity matrix.
-- source:
--   Holevo, The Capacity of Quantum Channel with General Signal States, arXiv:quant-ph/9611023v1, §3, p.3

import Mathlib

namespace HolevoCQ

/-- Holevo, *The Capacity of Quantum Channel with General Signal States*,
arXiv:quant-ph/9611023v1, §3, p.3: the tensor power `S̄^{⊗n} = S̄ ⊗ ⋯ ⊗ S̄` (n factors) of an
operator `ρ` on `H = ℂ^D`, an operator on `H^{⊗n}`.

**Formalization Note.** `H^{⊗n}` is `ℂ^{Fin n → D}`: a basis vector of `H^{⊗n}` is a word
`(j₁, …, jₙ)` of basis indices, and the matrix entry is `∏_l ρ_{a_l b_l}`. At `n = 0` this is the
`1 × 1` matrix `(1)`. -/
def tensorPowMat {D : Type} (ρ : Matrix D D ℂ) (n : ℕ) : Matrix (Fin n → D) (Fin n → D) ℂ :=
  Matrix.of fun a b => ∏ l, ρ (a l) (b l)

end HolevoCQ


