-- Prove2me | Definitions.Def_KallMayerSLP_ICC_KAlpha
-- name    : KallMayerSLP_ICC_KAlpha
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:11:39.702748+00:00
-- url     : https://prove2.me/theorems/0e4acccb-2e5c-42a9-88a2-aa673c4e6d91
-- title:
--   The evaluation function $K_\alpha(x)$
-- statement:
--   For $\alpha\in\mathbb R$, with $\bar t=\mathbb E_\xi[t(\xi)]$ and $\bar h=\mathbb E_\xi[h(\xi)]$,
--   $$
--   K_\alpha(x)=\alpha(\bar t x-\bar h)+(1-2\alpha)\,\mathbb E_\xi\big[\zeta^+(x,\xi)\big].
--   $$
--   It evaluates the quality measure $\rho^\alpha_{\mathrm{sic}}(\vartheta)=(1-\alpha)\mathbb E[\vartheta^+]-\alpha\mathbb E[\vartheta^-]$ at $\vartheta=\zeta(x,\xi)$, and $K_\alpha(x)\le 0$ is the constraint that the expected positive part is at most the fraction $\alpha$ of the expected absolute value.
--
--   **Formalization Note** $\bar t$ and $\bar h$ are Bochner integrals against the law `P` of $\xi$.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §4.1.1, p.153 (PDF 163)

import Mathlib
import Definitions.Def_KallMayerSLP_ICC_K

open MeasureTheory Matrix

namespace KallMayerSLP.ICC

/-- **The evaluation function `K_α(x) = α(t̄x − h̄) + (1 − 2α)𝔼_ξ[ζ⁺(x, ξ)]`.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §4.1.1, p.153 (PDF 163), with
`t̄ = 𝔼_ξ[t(ξ)]` and `h̄ = 𝔼_ξ[h(ξ)]` (below (4.15)).

**Formalization Note.** `t̄` is the Bochner integral of the vector-valued `t` against the law `P`
of `ξ`, and `h̄` that of `h`. -/
noncomputable def KAlpha {Ξ : Type*} [MeasurableSpace Ξ] {n : ℕ} (P : Measure Ξ)
    (t : Ξ → Fin n → ℝ) (h : Ξ → ℝ) (α : ℝ) (x : Fin n → ℝ) : ℝ :=
  α * ((∫ ξ, t ξ ∂P) ⬝ᵥ x - ∫ ξ, h ξ ∂P) + (1 - 2 * α) * K P t h x

end KallMayerSLP.ICC


