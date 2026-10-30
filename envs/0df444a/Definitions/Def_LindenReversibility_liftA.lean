-- Prove2me | Definitions.Def_LindenReversibility_liftA
-- name    : LindenReversibility_liftA
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:16:33.61418+00:00
-- url     : https://prove2.me/theorems/c8883194-6ddb-4b7f-b88d-b2eef7c193f3
-- title:
--   Alice's local operator $K\otimes I\otimes I$ on the joint system
-- statement:
--   Let $A$, $B$, $C$ be the index sets of Alice's, Bob's and Claire's systems; the joint system is $\mathbb C^A\otimes(\mathbb C^B\otimes\mathbb C^C)$. For an operator $K$ on Alice's system,
--
--   $$
--   \operatorname{lift}_A(K) = K\otimes I_B\otimes I_C .
--   $$
--
--   This is how a local operation of Alice, such as the projector $P_k\otimes I\otimes I$ of eq. (7), acts on the joint state.
--
--   **Formalization Note** Matrices on the joint system are indexed by $A\times(B\times C)$, Alice first; the tensor product is the Kronecker product.
-- source:
--   Linden, Popescu, Schumacher, Westmoreland, Reversibility of local transformations of multiparticle entanglement, arXiv:quant-ph/9912039v1, eq. (7), p.2

import Mathlib

namespace LindenReversibility

/-- Linden, Popescu, Schumacher, Westmoreland, arXiv:quant-ph/9912039v1, p.2 (eq. (7): the
operator `P_k ⊗ I ⊗ I`) and p.3 (eq. (14)): an operator `K` on Alice's (the first factor `A`) local system,
acting on the joint system as `K ⊗ 1_B ⊗ 1_C`.

**Formalization Note.** The joint index type is `A × (B × C)`: Alice is the first factor and
Bob-Claire the second (so `QAlgorithms.traceLeft` traces out Alice and
`QAlgorithms.traceRight` traces out Bob-Claire). `Matrix.kronecker X Y (i₁, i₂) (j₁, j₂) =
X i₁ j₁ * Y i₂ j₂`. -/
def liftA {A B C : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq C] (K : Matrix A A ℂ) :
    Matrix (A × (B × C)) (A × (B × C)) ℂ :=
  Matrix.kronecker K (1 : Matrix (B × C) (B × C) ℂ)

end LindenReversibility


