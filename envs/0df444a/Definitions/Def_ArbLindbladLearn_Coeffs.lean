-- Prove2me | Definitions.Def_ArbLindbladLearn_Coeffs
-- name    : ArbLindbladLearn_Coeffs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:22:02.93942+00:00
-- url     : https://prove2.me/theorems/502d5437-3238-45b4-ab10-6447cfe65f1a
-- title:
--   Pauli coefficients $(h, \gamma)$ of an $n$-qubit Lindbladian
-- statement:
--   An $n$-qubit Lindbladian is written in the Pauli basis as
--   $$\mathcal L(\rho)=\sum_{a\neq0}-\mathrm i\,h_a[P_a,\rho]+\sum_{a,b\neq0}\gamma_{ab}\Big(P_a\rho P_b-\tfrac12\{P_bP_a,\rho\}\Big)$$
--   with Hamiltonian coefficients $h_a\in\mathbb R$ and dissipative coefficients $\gamma_{ab}\in\mathbb C$. This structure records the two families of coefficients, indexed by Pauli labels.
--
--   It is the object the learner of Corollary 4.7 estimates, and the input of the generator `gen`.
--
--   **Formalization Note** Pauli labels are the public `Pauli n = Fin n → Fin 4` (letters $I, X, Y, Z$) instead of the paper's binary labels $(z,x)\in\mathbb F_2^{2n}$; since $(-\mathrm i)ZX=Y$, both index the same operators and $0$ is the identity. The values $h_0$ and $\gamma_{0b},\gamma_{a0}$ are never used.
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Definition 2.6, eq. (8), p.14; Definition 2.2, p.12

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn

open LindbladTolerant.Testing

/-- The coefficients of an `n`-qubit Lindbladian in the Pauli basis (Definition 2.6, eq. (8),
Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.14): Hamiltonian coefficients `h a ∈ ℝ` and dissipative (Kossakowski)
coefficients `γ a b ∈ ℂ`, indexed by Pauli labels.

**Formalization Note** Pauli labels are the public `Pauli n = Fin n → Fin 4` (letters
`0 = I, 1 = X, 2 = Y, 3 = Z`) instead of the paper's binary labels `(z, x) ∈ 𝔽₂²ⁿ` with
`P_(z,x) = ⊗ᵢ (−i)^{zᵢxᵢ} Z^{zᵢ} X^{xᵢ}` (Definition 2.2, p.12). The two label sets index the same
Hermitian operators, since `(−i)ZX = Y`; the zero label is the identity in both. The paper only
uses `h_a` for `a ≠ 0` and `γ_ab` for `a, b ≠ 0`; the values at the identity label are never
used (the generator `gen` and every statement restrict to nonidentity labels). -/
structure Coeffs (n : ℕ) where
  /-- Hamiltonian coefficients `h_a`. -/
  h : Pauli n → ℝ
  /-- Dissipative coefficients `γ_ab`. -/
  γ : Pauli n → Pauli n → ℂ

end ArbLindbladLearn


