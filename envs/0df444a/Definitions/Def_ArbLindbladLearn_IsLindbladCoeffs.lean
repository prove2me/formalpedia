-- Prove2me | Definitions.Def_ArbLindbladLearn_IsLindbladCoeffs
-- name    : ArbLindbladLearn_IsLindbladCoeffs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:23:37.462525+00:00
-- url     : https://prove2.me/theorems/8d701462-d4e7-470f-9432-00aaeeafd6b2
-- title:
--   Valid Lindbladian coefficients: Kossakowski matrix Hermitian PSD
-- statement:
--   Coefficients $(h,\gamma)$ define a Lindbladian when the **Kossakowski matrix** $\gamma=(\gamma_{ab})_{a,b\neq0}\in\mathbb C^{(4^n-1)\times(4^n-1)}$, indexed by the nonidentity Pauli labels, is Hermitian and positive semidefinite:
--   $$\gamma=\gamma^\dagger,\qquad \gamma\succeq0 .$$
--   The Hamiltonian coefficients are real by their type.
--
--   This is the class of generators of quantum dynamical semigroups in the Pauli basis (GKSL form).
--
--   **Formalization Note** Mathlib's `Matrix.PosSemidef` includes Hermiticity; only the block of nonidentity labels is constrained.
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Definition 2.6, p.14

import Mathlib
import Definitions.Def_ArbLindbladLearn_Coeffs

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn

open LindbladTolerant.Testing

/-- Validity of Lindbladian coefficients (Definition 2.6, Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.14):
the Kossakowski matrix `γ = (γ_ab)_{a,b≠0}`, indexed by the `4ⁿ − 1` nonidentity labels, is
Hermitian and positive semidefinite (`γ = γ†`, `γ ⪰ 0`). The Hamiltonian coefficients are real by
their type.

**Formalization Note** Mathlib's `Matrix.PosSemidef` includes Hermiticity. Only the block of
nonidentity labels is constrained; entries with an identity index are unused. -/
def IsLindbladCoeffs {n : ℕ} (c : Coeffs n) : Prop :=
  (Matrix.of fun a b : {a : Pauli n // a ≠ 0} => c.γ a b).PosSemidef

end ArbLindbladLearn


