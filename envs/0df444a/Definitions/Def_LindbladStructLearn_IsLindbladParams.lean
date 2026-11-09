-- Prove2me | Definitions.Def_LindbladStructLearn_IsLindbladParams
-- name    : LindbladStructLearn_IsLindbladParams
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:47:08.495777+00:00
-- url     : https://prove2.me/theorems/681dd978-ef8a-4492-8440-23648cb76223
-- title:
--   Physical Lindbladian parameters ($\alpha$ imaginary, $D \succeq 0$)
-- statement:
--   A coefficient vector $\lambda$ describes a Lindbladian in the sense of Definition 2.1 when, writing $\alpha_P = \lambda_{P,I}$ and $D_{P_1,P_2} = \lambda_{P_1,P_2}$ for $P_1,P_2 \ne I$:
--
--   1. $\lambda_{I,Q} = 0$ for every $Q$ (pairs with $P_1 = I$ are not parameters);
--   2. every $\alpha_P$ is purely imaginary ($\mathrm{Re}\,\alpha_P = 0$);
--   3. the matrix $D = (\lambda_{P_1,P_2})_{P_1,P_2\ne I}$ is positive semidefinite.
--
--   These are exactly the coefficient vectors for which $\mathcal L_\lambda$ generates a quantum dynamical semigroup.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Definition 2.1, Eqs. (2.4)–(2.5), p.13

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- Physical Lindbladian parameters (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Definition 2.1, Eqs. (2.4)–(2.5), p.13): writing
`λ_(P,I) = α_P` and `λ_(P₁,P₂) = D_(P₁,P₂)` (`P₁, P₂ ≠ I`), `α` is purely imaginary and `D` is
positive semidefinite.

**Formalization Note** Coefficient vectors are functions on all pairs of `n`-qubit Paulis; the
first clause is the convention that pairs with `P₁ = I` carry `0` (they are not parameters).
`D` is the matrix indexed by the non-identity Paulis; positive semidefinite over `ℂ` (with
`ComplexOrder`). "Purely imaginary" is `Re α_P = 0` (zero included). -/
def IsLindbladParams {n : ℕ} (x : Pauli n × Pauli n → ℂ) : Prop :=
  (∀ Q : Pauli n, x (0, Q) = 0) ∧ (∀ P : Pauli n, P ≠ 0 → (x (P, 0)).re = 0) ∧
    Matrix.PosSemidef (fun P Q : {P : Pauli n // P ≠ 0} => x (P.1, Q.1))

end LindbladStructLearn


