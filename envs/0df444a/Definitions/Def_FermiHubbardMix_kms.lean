-- Prove2me | Definitions.Def_FermiHubbardMix_kms
-- name    : FermiHubbardMix_kms
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:30:23.697195+00:00
-- url     : https://prove2.me/theorems/a2f63f37-be5e-4c34-a6b4-73f0bc92e30d
-- title:
--   KMS detailed balance
-- statement:
--   Let $\rho$ be a positive definite density matrix and $\mathcal L$ a linear superoperator, with Hilbert–Schmidt adjoint $\mathcal L^\dagger$, i.e. $\operatorname{tr}(X^\dagger\mathcal L[Y])=\operatorname{tr}((\mathcal L^\dagger[X])^\dagger Y)$ for all $X,Y$. Then $\mathcal L$ satisfies **KMS detailed balance** (Definition C.1) if
--   $$
--   \mathcal L^\dagger[\cdot]=\rho^{-1/2}\,\mathcal L\bigl(\rho^{1/2}(\cdot)\rho^{1/2}\bigr)\,\rho^{-1/2}.
--   $$
--   This is the symmetry that makes the Gibbs state a stationary state of the CKG Lindbladian.
--
--   **Formalization Note** The condition is stated through the defining property of $\mathcal L^\dagger$: $\operatorname{tr}(X^\dagger\mathcal L[Y])=\operatorname{tr}\bigl((\rho^{-1/2}\mathcal L(\rho^{1/2}X\rho^{1/2})\rho^{-1/2})^\dagger Y\bigr)$ for all $X,Y$, with $\rho^{1/2}$ the positive square root and $\rho^{-1/2}$ its inverse.
-- source:
--   Bakshi, Moitra, Tan, Algorithmic Aspects of the Fermi–Hubbard Model, arXiv:2604.08408 (held version, sha256 055b8f8f…), Definition C.1, p.88

import Mathlib
import Definitions.Def_FermiHubbardMix_parityOp
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
noncomputable section

namespace FermiHubbardMix

/-- **Definition C.1 (KMS detailed balance)** (arXiv:2604.08408, held version sha256 055b8f8f…,
p.88): with `L†` the Hilbert–Schmidt adjoint of `L` (`tr(X† L[Y]) = tr((L†[X])† Y)`), `L` satisfies
KMS detailed balance for `ρ` if `L†[·] = ρ^{-1/2} L(ρ^{1/2} (·) ρ^{1/2}) ρ^{-1/2}`.

**Formalization Note** The condition is stated through the defining property of `L†`: for all
`X, Y`, `tr(X† L[Y]) = tr((ρ^{-1/2} L(ρ^{1/2} X ρ^{1/2}) ρ^{-1/2})† Y)`. `ρ^{1/2}` is the
continuous-functional-calculus square root `CFC.sqrt ρ` and `ρ^{-1/2}` its matrix inverse; the
condition is meant for positive definite `ρ` (here, a Gibbs state). -/
def IsKMS {N : ℕ} (ρ : Op N) (L : Op N →ₗ[ℂ] Op N) : Prop :=
  ∀ X Y : Op N, (Xᴴ * L Y).trace =
    (((CFC.sqrt ρ)⁻¹ * L (CFC.sqrt ρ * X * CFC.sqrt ρ) * (CFC.sqrt ρ)⁻¹)ᴴ * Y).trace

end FermiHubbardMix


