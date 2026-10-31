-- Prove2me | Definitions.Def_KallMayerSLP_CondExp_rhoSicMinus
-- name    : KallMayerSLP_CondExp_rhoSicMinus
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:10:21.808266+00:00
-- url     : https://prove2.me/theorems/21cdb9f3-3616-4872-bbfd-9c3f876997eb
-- title:
--   Integrated-chance measure $\rho^-_{\mathrm{sic}}(\vartheta)=\mathbb E[\vartheta^-]$
-- statement:
--   For an integrable real random variable $\vartheta$, with negative part $z^-=\max\{0,-z\}$, the quality measure behind separate integrated chance constraints is
--   $$
--   \rho^-_{\mathrm{sic}}(\vartheta)=\mathbb E[\vartheta^-].
--   $$
--   Losses are modelled as negative values of $\vartheta$, so $\rho^-_{\mathrm{sic}}(\vartheta)$ is the expected size of the loss over all outcomes, not conditioned on a loss occurring. A separate integrated chance constraint bounds $\mathbb E[\zeta^-(x,\xi)]$ from above, in place of the probability bound of a chance constraint. The same measure reappears in Chapter 2, §7.2 (Proposition 7.4, p.186) as the risk measure (D2) on $\mathcal L^1_1$.
--
--   **Formalization Note** A Bochner integral, which is $0$ for a non-integrable function; the book's domain is $\mathcal L^1_1$ and every statement here assumes integrability.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, eq. (4.3), p.149

import Mathlib

open MeasureTheory

namespace KallMayerSLP.CondExp

/-- The integrated-chance-constraint quality measure `ρ⁻_sic(ϑ) := 𝔼[ϑ⁻]`.
Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, eq. (4.3), p.149 (PDF 159), with the
negative part `z⁻ = max{0, -z}` of p.149.

**Formalization Note** `ϑ⁻` is written `max (-ϑ ω) 0`. A Bochner integral: the book's domain is
`𝓛¹₁`, so every statement about `rhoSicMinus` assumes `ϑ` integrable. -/
noncomputable def rhoSicMinus {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (ϑ : Ω → ℝ) : ℝ :=
  ∫ ω, max (-ϑ ω) 0 ∂μ

end KallMayerSLP.CondExp


