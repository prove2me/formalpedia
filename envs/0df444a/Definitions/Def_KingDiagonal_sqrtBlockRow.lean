-- Prove2me | Definitions.Def_KingDiagonal_sqrtBlockRow
-- name    : KingDiagonal_sqrtBlockRow
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:20.201502+00:00
-- url     : https://prove2.me/theorems/d3a4bb30-c568-4845-af5b-7965e27b396d
-- title:
--   Block rows $V_i$ of the square root $\big((I\otimes\Psi)(\tau)\big)^{1/2}$ (eq. 16)
-- statement:
--   Let $M$ be a matrix on $\mathbb C^n\otimes\mathbb C^m$ (an $n\times n$ block matrix with $m\times m$ blocks). Write its square root $M^{1/2}$ as a column of $n$ block rows,
--
--   $$
--   M^{1/2} = \begin{pmatrix} V_1 \\ \vdots \\ V_n\end{pmatrix},
--   $$
--
--   so that $V_i$ is the $m\times nm$ matrix with entries $(V_i)_{a,c} = (M^{1/2})_{(i,a),c}$. In King's argument $M = (I\otimes\Psi)(\tau)$ is positive semidefinite and $M = (V_iV_j^*)_{ij}$ (eq. (17)).
--
--   **Formalization Note** $M^{1/2}$ is `cfc Real.sqrt M` (continuous functional calculus), the positive square root on positive semidefinite $M$. The page writes $V_i$ as $k\times kn$ because the output dimension of $\Psi$ is $k$ there; here it is an arbitrary $m$.
-- source:
--   King, An application of a matrix inequality in quantum information theory, arXiv:quant-ph/0412046v1, eq. (16), p.5

import Mathlib

namespace KingDiagonal

/-- King, arXiv:quant-ph/0412046v1, eq. (16), p.5: `V_1, …, V_n` are the block rows of the square
root of `(I ⊗ Ψ)(τ)`, i.e. `((I ⊗ Ψ)(τ))^{1/2}` is the column `(V_1; …; V_n)`. Here, for any
matrix `M` on `C^n ⊗ C^m` (block index first), `sqrtBlockRow M i` is the `i`-th block row of
`M^{1/2}`: the `m × nm` matrix with entries `(V_i)_{a, c} = (M^{1/2})_{(i,a), c}`.

**Formalization Note.** `M^{1/2}` is `cfc Real.sqrt M`, the continuous functional calculus; it is
the positive square root when `M` is positive semidefinite, which is the case where the paper uses
it (`M = (I ⊗ Ψ)(τ)`). The page writes `k × kn` with the output dimension of `Ψ` equal to `k`; here
the output index type `m` is arbitrary. -/
noncomputable def sqrtBlockRow {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
    [DecidableEq m] (M : Matrix (n × m) (n × m) ℂ) (i : n) : Matrix m (n × m) ℂ :=
  Matrix.of fun a c => (cfc Real.sqrt M) (i, a) c

end KingDiagonal


