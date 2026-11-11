-- Prove2me | Definitions.Def_ArbLindbladLearn_StrengthLE
-- name    : ArbLindbladLearn_StrengthLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:25:20.906193+00:00
-- url     : https://prove2.me/theorems/b27238ed-30aa-48df-87aa-b185bc7baa03
-- title:
--   Dynamical strength bound $\|\mathcal L^\dagger\|_{\infty\to\infty}\le\Lambda$
-- statement:
--   The **dynamical strength** of a Lindbladian is $\|\mathcal L^\dagger\|_{\infty\to\infty}=\sup_{A\neq0}\|\mathcal L^\dagger(A)\|_\infty/\|A\|_\infty$, where $\mathcal L^\dagger$ is the Hilbert–Schmidt adjoint, $\langle A,\mathcal L(B)\rangle=\langle\mathcal L^\dagger(A),B\rangle$ with $\langle A,B\rangle=\mathrm{tr}(A^\dagger B)$. The predicate says that this strength is at most $\Lambda$:
--   $$\|\mathcal L^\dagger(A)\|_\infty\le\Lambda\,\|A\|_\infty\quad\text{for every operator }A .$$
--
--   The paper assumes this known bound throughout; it is the only prior information about $\mathcal L$ the learner gets.
--
--   **Formalization Note** $\mathcal L^\dagger$ is the conjugate transpose of the superoperator matrix; the bound is over all complex operators, with the spectral norm. It forces $\Lambda\ge0$.
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Definition 2.8 and the standing assumption, p.14; induced norm and adjoint, pp.11–12

import Mathlib
import Definitions.Def_ArbLindbladLearn_gen
import Definitions.Def_ArbLindbladLearn_opNorm

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn

open LindbladTolerant.Testing

/-- The dynamical-strength bound `‖ℒ†‖_{∞→∞} ≤ Λ` (Definition 2.8 and the standing assumption
after it, Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.14; the induced norm and the adjoint are defined on
pp.11–12).

**Formalization Note** `ℒ†` is the Hilbert–Schmidt adjoint, `⟨A, ℒ(B)⟩ = ⟨ℒ†(A), B⟩` with
`⟨A, B⟩ = tr(A†B)`; on superoperator matrices it is the conjugate transpose `(gen c)ᴴ`. The induced
norm bound `sup_{A≠0} ‖ℒ†(A)‖_∞/‖A‖_∞ ≤ Λ` is stated as `‖ℒ†(A)‖_∞ ≤ Λ‖A‖_∞` for every operator
`A` (complex, not only Hermitian), with the spectral norm `opNorm`. It forces `Λ ≥ 0`. -/
def StrengthLE {n : ℕ} (c : Coeffs n) (Λ : ℝ) : Prop :=
  ∀ A : Op (Qubits n), opNorm (applySuper (gen c)ᴴ A) ≤ Λ * opNorm A

end ArbLindbladLearn


