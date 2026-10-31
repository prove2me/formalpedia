-- Prove2me | Definitions.Def_KallMayerSLP_SimpleRecourse_expectedSRT
-- name    : KallMayerSLP_SimpleRecourse_expectedSRT
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:12:25.928276+00:00
-- url     : https://prove2.me/theorems/be89aa6d-d049-40e0-8d6e-19de52a5dc07
-- title:
--   Expected SRT function $\Phi(z)=\mathbb E[\varphi(z,\tilde\xi)]$
-- statement:
--   Let $\tilde\xi$ be a real random variable with distribution $\mathbb P_{\tilde\xi}$ and assume $\mathbb E_{\tilde\xi}[\tilde\xi]$ exists. The **expected simple recourse type function** is
--
--   $$
--   \Phi(z) := \mathbb E_{\tilde\xi}[\varphi(z,\tilde\xi)] = \int_{-\infty}^{\infty}\bigl(\alpha[\xi-z]^+ + \beta[\xi-z]^-\bigr)\,\mathbb P_{\tilde\xi}(d\xi) - \gamma .
--   $$
--
--   Conditional versions $\Phi_{|I}(z)=\mathbb E_{\tilde\xi}[\varphi(z,\tilde\xi)\mid \tilde\xi\in I]$ are obtained by replacing $\mathbb P_{\tilde\xi}$ by the conditional law $\mathbb P_{\tilde\xi}(\cdot\mid I)$.
--
--   **Formalization Note** The argument is the law $P=\mathbb P_{\tilde\xi}$, a measure on $\mathbb R$; the definition is the printed right-hand side. That $P$ is a probability measure and that $\tilde\xi$ is integrable are hypotheses of the theorems.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, Definition 2.3, pp.228–229 (PDF 237–238)

import Mathlib

open MeasureTheory

namespace KallMayerSLP.SimpleRecourse

/-- **Expected simple recourse type (ESRT) function, Definition 2.3.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, Definition 2.3, pp.228–229
(PDF 237–238): for the distribution `ℙ_ξ̃` of a real random variable `ξ̃`, provided `𝔼_ξ̃[ξ̃]`
exists,
`Φ(z) := 𝔼_ξ̃[φ(z, ξ̃)] = ∫_{−∞}^{∞} (α · [ξ − z]⁺ + β · [ξ − z]⁻) ℙ_ξ̃(dξ) − γ`.

**Formalization Note.** `P` is the distribution `ℙ_ξ̃` of `ξ̃`, a measure on `ℝ`; the definition
is the right-hand side as printed. The existence of `𝔼_ξ̃[ξ̃]` (integrability of the identity under
`P`) and `IsProbabilityMeasure P` are hypotheses of the theorems. Conditional versions
`Φ_{|I}` are `expectedSRT α β γ P[|I]` (`ProbabilityTheory.cond`). -/
noncomputable def expectedSRT (α β γ : ℝ) (P : Measure ℝ) (z : ℝ) : ℝ :=
  ∫ ξ, (α * (ξ - z)⁺ + β * (ξ - z)⁻) ∂P - γ

end KallMayerSLP.SimpleRecourse


