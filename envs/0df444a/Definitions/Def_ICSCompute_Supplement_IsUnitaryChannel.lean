-- Prove2me | Definitions.Def_ICSCompute_Supplement_IsUnitaryChannel
-- name    : ICSCompute_Supplement_IsUnitaryChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T15:01:44.793455+00:00
-- url     : https://prove2.me/theorems/8b9fd3eb-f09a-4111-b269-dbad004fdf6c
-- title:
--   Unitary quantum channel
-- statement:
--   Let $\Phi$ be a linear map from the matrices on a register $H_\iota$ to the matrices on a register $H_\kappa$. Then $\Phi$ is a **unitary channel** if there is a matrix $U$ from $H_\iota$ to $H_\kappa$ with $U^\dagger U=I$ and $UU^\dagger=I$ such that
--
--   $$\Phi(X)=U\,X\,U^\dagger\qquad\text{for every matrix }X.$$
--
--   For qubit registers $S(r)=\mathbb C^{2^r}$ and $S(\ell)$ the two unitarity conditions force $r=\ell$, so this is the paper's notion of an $n$-to-$n$ qubit channel that acts as conjugation by a unitary. It is the property "the generated channel is unitary" in Theorems 1.1, 5.1 and 5.2.
--
--   **Formalization Note** The paper asks for $\Phi(\rho)=U\rho U^\dagger$ on every $n$-qubit state $\rho$; since $\Phi$ is linear and states span all matrices, this is the same as the identity on every matrix. A map of this form is automatically a quantum channel.
-- source:
--   Shmueli, What Can Be Computed with Indefinite Causal Structure?, arXiv:2610.40573 (version of 2026-11-03, sha256 d3e36399…b606), Definition 4.6, p.20 (PDF p.22)

import Mathlib

namespace ICSCompute.Supplement

/-- **Unitary quantum channel** (Shmueli, *What Can Be Computed with Indefinite Causal
Structure?*, arXiv:2610.40573, version of 2026-11-03, sha256 d3e36399…b606, Definition 4.6,
p.20 (PDF p.22)): "Let `n ∈ ℕ ∪ {0}` and let `C` be an `n`-to-`n` qubit quantum channel, as in
Definition 3.13. We say that `C` is unitary if there is a unitary matrix `U_C ∈ ℂ^{2ⁿ×2ⁿ}` such
that `C(ρ) = U_C ρ U_C†` for every `n`-qubit state `ρ`."

**Formalization Note** The input and output registers are index types `ι`, `κ`; `U` is a matrix
from `ι` to `κ` with `U†U = I` and `UU† = I`, which forces `|ι| = |κ|` and for `ι = κ` is
exactly membership in `Matrix.unitaryGroup`. For qubit registers `S(r)`, `S(ℓ)` it forces
`r = ℓ`, the paper's "`n`-to-`n`". The identity `Φ(X) = U X U†` is required for every matrix `X`,
which is equivalent to the paper's "for every state `ρ`" because `Φ` is linear and states span
all matrices; a map of this form is automatically a quantum channel. -/
def IsUnitaryChannel {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) : Prop :=
  ∃ U : Matrix κ ι ℂ, U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1 ∧
    ∀ X : Matrix ι ι ℂ, Φ X = U * X * U.conjTranspose

end ICSCompute.Supplement


