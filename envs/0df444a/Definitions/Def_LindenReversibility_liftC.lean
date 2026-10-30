-- Prove2me | Definitions.Def_LindenReversibility_liftC
-- name    : LindenReversibility_liftC
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:16:36.772885+00:00
-- url     : https://prove2.me/theorems/9a6f2627-12f3-4027-8be4-53cdd2f79cee
-- title:
--   Claire's local operator $I\otimes I\otimes K$ on the joint system
-- statement:
--   Let $A$, $B$, $C$ be the index sets of Alice's, Bob's and Claire's systems; the joint system is $\mathbb C^A\otimes(\mathbb C^B\otimes\mathbb C^C)$. For an operator $K$ on Claire's system,
--
--   $$
--   \operatorname{lift}_C(K) = I_A\otimes I_B\otimes K .
--   $$
--
--   This is how a local measurement or unitary of Claire acts on the joint state (p.3, (14)).
--
--   **Formalization Note** Matrices on the joint system are indexed by $A\times(B\times C)$; the tensor product is the Kronecker product.
-- source:
--   Linden, Popescu, Schumacher, Westmoreland, Reversibility of local transformations of multiparticle entanglement, arXiv:quant-ph/9912039v1, p.3, eq. (14)

import Mathlib

namespace LindenReversibility

/-- Linden, Popescu, Schumacher, Westmoreland, arXiv:quant-ph/9912039v1, p.2 (eq. (7): the
operator `P_k ⊗ I ⊗ I`) and p.3 (eq. (14)): an operator `K` on Claire's (the factor `C`) local system,
acting on the joint system as `1_A ⊗ 1_B ⊗ K`.

**Formalization Note.** The joint index type is `A × (B × C)`: Alice is the first factor and
Bob-Claire the second (so `QAlgorithms.traceLeft` traces out Alice and
`QAlgorithms.traceRight` traces out Bob-Claire). `Matrix.kronecker X Y (i₁, i₂) (j₁, j₂) =
X i₁ j₁ * Y i₂ j₂`. -/
def liftC {A B C : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq C] (K : Matrix C C ℂ) :
    Matrix (A × (B × C)) (A × (B × C)) ℂ :=
  Matrix.kronecker (1 : Matrix A A ℂ) (Matrix.kronecker (1 : Matrix B B ℂ) K)

end LindenReversibility


