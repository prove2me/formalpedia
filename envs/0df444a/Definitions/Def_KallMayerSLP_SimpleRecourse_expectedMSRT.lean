-- Prove2me | Definitions.Def_KallMayerSLP_SimpleRecourse_expectedMSRT
-- name    : KallMayerSLP_SimpleRecourse_expectedMSRT
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:12:29.375446+00:00
-- url     : https://prove2.me/theorems/624107df-e736-4389-8433-e5ea78665960
-- title:
--   Expected MSRT function $\Psi(z)=\mathbb E[\psi(z,\tilde\xi)]$
-- statement:
--   With $F_{\tilde\xi}$ the distribution function of the real random variable $\tilde\xi$, the **expected MSRT function** is
--
--   $$
--   \Psi(z) = \mathbb E_{\tilde\xi}[\psi(z,\tilde\xi)] = \int_{-\infty}^{\infty}\sum_{k=0}^{K-1}\bigl\{\alpha_k[\xi-z-u_k]^+ + \beta_k[\xi-z+l_k]^-\bigr\}\,dF_{\tilde\xi}(\xi) - \gamma .
--   $$
--
--   It is the second-stage cost of the multiple simple recourse problem (2.59).
--
--   **Formalization Note** The argument is the law $P$ of $\tilde\xi$ (integration against $dF_{\tilde\xi}$ is integration against $P$); the definition is the last printed expression.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, Definition 2.4, pp.237–238 (PDF 246–247)

import Mathlib

open MeasureTheory

namespace KallMayerSLP.SimpleRecourse

/-- **Expected MSRT function, Definition 2.4.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, Definition 2.4, pp.237–238
(PDF 246–247):
`Ψ(z) = 𝔼_ξ̃[ψ(z, ξ̃)] = ∫_{−∞}^{∞} Σ_{k=0}^{K−1} {α_k · [ξ − z − u_k]⁺ + β_k · [ξ − z + l_k]⁻} dF_ξ̃(ξ) − γ`.

**Formalization Note.** `P` is the distribution of `ξ̃` (a measure on `ℝ`; integrating against
`dF_ξ̃` is integrating against `P`); the definition is the last expression as printed.
`IsProbabilityMeasure P` and the integrability of `ξ̃` are hypotheses of the theorems. -/
noncomputable def expectedMSRT {K : ℕ} (α β u l : Fin K → ℝ) (γ : ℝ) (P : Measure ℝ) (z : ℝ) : ℝ :=
  ∫ ξ, ∑ k, (α k * (ξ - z - u k)⁺ + β k * (ξ - z + l k)⁻) ∂P - γ

end KallMayerSLP.SimpleRecourse


