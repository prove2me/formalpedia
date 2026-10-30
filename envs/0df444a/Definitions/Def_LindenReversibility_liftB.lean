-- Prove2me | Definitions.Def_LindenReversibility_liftB
-- name    : LindenReversibility_liftB
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:16:34.317997+00:00
-- url     : https://prove2.me/theorems/9e61d9c9-acdc-4b5e-9f45-741b9578d643
-- title:
--   Bob's local operator $I\otimes K\otimes I$ on the joint system
-- statement:
--   Let $A$, $B$, $C$ be the index sets of Alice's, Bob's and Claire's systems; the joint system is $\mathbb C^A\otimes(\mathbb C^B\otimes\mathbb C^C)$. For an operator $K$ on Bob's system,
--
--   $$
--   \operatorname{lift}_B(K) = I_A\otimes K\otimes I_C .
--   $$
--
--   This is how a local measurement or unitary of Bob acts on the joint state (p.3, (14) and the step after (15)).
--
--   **Formalization Note** Matrices on the joint system are indexed by $A\times(B\times C)$; the tensor product is the Kronecker product.
-- source:
--   Linden, Popescu, Schumacher, Westmoreland, Reversibility of local transformations of multiparticle entanglement, arXiv:quant-ph/9912039v1, p.3, eq. (14) and the paragraph after (15)

import Mathlib

namespace LindenReversibility

/-- Linden, Popescu, Schumacher, Westmoreland, arXiv:quant-ph/9912039v1, p.2 (eq. (7): the
operator `P_k ⊗ I ⊗ I`) and p.3 (eq. (14)): an operator `K` on Bob's (the factor `B`) local system,
acting on the joint system as `1_A ⊗ K ⊗ 1_C`.

**Formalization Note.** The joint index type is `A × (B × C)`: Alice is the first factor and
Bob-Claire the second (so `QAlgorithms.traceLeft` traces out Alice and
`QAlgorithms.traceRight` traces out Bob-Claire). `Matrix.kronecker X Y (i₁, i₂) (j₁, j₂) =
X i₁ j₁ * Y i₂ j₂`. -/
def liftB {A B C : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq C] (K : Matrix B B ℂ) :
    Matrix (A × (B × C)) (A × (B × C)) ℂ :=
  Matrix.kronecker (1 : Matrix A A ℂ) (Matrix.kronecker K (1 : Matrix C C ℂ))

end LindenReversibility


