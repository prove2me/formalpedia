-- Prove2me | Definitions.Def_WildeQIT_QMemory_vonNeumann
-- name    : WildeQIT_QMemory_vonNeumann
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:56:12.31793+00:00
-- url     : https://prove2.me/theorems/2d2fa1ba-218e-4f71-8ea9-e43db5a4e5e5
-- title:
--   Quantum (von Neumann) entropy $H(\rho)=-\mathrm{Tr}\{\rho\log\rho\}$
-- statement:
--   Let $\rho$ be a density operator on a finite-dimensional Hilbert space $\mathcal H$. Its **quantum entropy** (von Neumann entropy) is
--
--   $$
--   H(\rho)\equiv-\mathrm{Tr}\{\rho\log\rho\},
--   $$
--
--   with the logarithm in base 2, so entropy is measured in bits. If $\rho=\sum_x p_X(x)|x\rangle\langle x|$ is a spectral decomposition, $H(\rho)=-\sum_x p_X(x)\log p_X(x)$ is the Shannon entropy of the eigenvalues, with $0\log 0=0$. We write $H(A)_\rho$ or $H(\rho_A)$ for the entropy of the state of system $A$.
--
--   This is the basic quantity of the chapter: conditional entropy, coherent information and mutual information are all built from it.
--
--   **Formalization Note** Operators are complex matrices indexed by a finite type. $\log\rho$ is the continuous functional calculus `cfc (Real.logb 2) ρ`; since `Real.logb 2 0 = 0` it is the logarithm on the support, which gives $0\log 0=0$. On a non-Hermitian matrix the functional calculus returns $0$, so the value is $0$ there; the entropy is only applied to density operators.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Definition 11.1.1, eq. (11.1), p. 320

import Mathlib

namespace WildeQIT.QMemory

/-- **Quantum entropy** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8,
Definition 11.1.1, p. 320): for a density operator `ρ`, `H(ρ) ≡ −Tr{ρ log ρ}` (11.1).

**Formalization Note** Operators on a finite-dimensional Hilbert space are complex matrices
indexed by a finite type. The logarithm is base 2 (bits), the book's convention, and `log ρ` is
the continuous functional calculus `cfc (Real.logb 2) ρ`; since `Real.logb 2 0 = 0`, this is the
logarithm on the support of `ρ`, so the convention `0 log 0 = 0` holds. On a non-Hermitian
matrix `cfc` returns `0`, so the value there is `0`; the entropy is only applied to density
operators. -/
noncomputable def vonNeumann {n : Type} [Fintype n] [DecidableEq n] (ρ : Matrix n n ℂ) : ℝ :=
  -(Matrix.trace (ρ * cfc (Real.logb 2) ρ)).re

end WildeQIT.QMemory


