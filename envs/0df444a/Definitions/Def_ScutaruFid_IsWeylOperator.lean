-- Prove2me | Definitions.Def_ScutaruFid_IsWeylOperator
-- name    : ScutaruFid_IsWeylOperator
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:56:58.463698+00:00
-- url     : https://prove2.me/theorems/c343ffa0-e951-4ab5-bcff-4bc6ff409f0c
-- title:
--   Weyl operator $W(\alpha,\tau)$ on $L^2(\mathbb R)$
-- statement:
--   With position $(Q\psi)(x)=x\psi(x)$ and momentum $(P\psi)(x)=-i\,\psi'(x)$ ($\hbar=1$), the **Weyl (displacement) operator** $W(\alpha,\tau)$, $\alpha,\tau\in\mathbb R$, is the bounded operator on $L^2(\mathbb R)$ acting by
--
--   $$
--   (W(\alpha,\tau)\psi)(x)=e^{i\tau(x-\alpha/2)}\,\psi(x-\alpha).
--   $$
--
--   It equals $\exp(i(\tau Q-\alpha P))$: conjugation by it shifts the mean of $Q$ by $\alpha$ and the mean of $P$ by $\tau$. Displaced states are $W(\alpha,\tau)\rho\,W(-\alpha,-\tau)$, and $\operatorname{trace}(W(\alpha,\tau)\rho)$ is the characteristic function of $\rho$.
--
--   **Formalization Note** `IsWeylOperator W α τ` states the formula above for every $\psi$ and almost every $x$; it determines $W$ uniquely.
-- source:
--   Scutaru, Fidelity for displaced squeezed thermal states and the oscillator semigroup, arXiv:quant-ph/9708013v1, p.2, the line after (10) and the line after (11) (definitions of W(α, τ), Q, P)

import Mathlib
import Definitions.Def_ScutaruFid_L2R

open MeasureTheory

namespace ScutaruFid

/-- **Weyl operator `W(α, τ)`**, eq. (10). Scutaru, arXiv:quant-ph/9708013v1, p.2, the line after
(10): "(W(α, τ)ψ)(x) = exp[iτ(x − α/2)]ψ(x − α)", with "(Qψ)(x) = xψ(x) and (Pψ)(x) = −i dψ(x)/dx".

`IsWeylOperator W α τ` says that the bounded operator `W` on `L²(ℝ)` acts on every `ψ` by
`(Wψ)(x) = exp(iτ(x − α/2)) ψ(x − α)` for almost every `x`.

**Formalization Note** This is the operator `exp(i(τQ − αP))` (with `ħ = 1`): it shifts the mean
of the position `Q` by `+α` and the mean of the momentum `P` by `+τ`. The characterization by an
a.e. formula determines `W` uniquely; `W(−α, −τ)` is its adjoint. -/
def IsWeylOperator (W : L2R →L[ℂ] L2R) (α τ : ℝ) : Prop :=
  ∀ ψ : L2R, (W ψ : ℝ → ℂ) =ᵐ[volume]
    fun x => Complex.exp (Complex.I * (τ : ℂ) * ((x : ℂ) - (α : ℂ) / 2)) * ψ (x - α)

end ScutaruFid


