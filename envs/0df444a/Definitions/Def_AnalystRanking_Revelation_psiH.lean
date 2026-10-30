-- Prove2me | Definitions.Def_AnalystRanking_Revelation_psiH
-- name    : AnalystRanking_Revelation_psiH
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:37:44.795268+00:00
-- url     : https://prove2.me/theorems/14061fe1-c56e-4471-982f-a0595fbf2296
-- title:
--   $\Psi^h_i(\sigma^h,\sigma^l)$, (A.11)
-- statement:
--   With $\chi=\rho\gamma(1-\gamma)$ and the other analyst's strategy $(\sigma^h,\sigma^l)$,
--   $$\Psi^h_i=\frac{1+\big[\sigma^h(1-\gamma+\tfrac{\chi}{1-\gamma})+(1-\sigma^l)(\gamma-\tfrac{\chi}{1-\gamma})\big](\varphi-1)}{\varphi-\big[\sigma^h(\gamma+\tfrac{\chi}{\gamma})+(1-\sigma^l)(1-\gamma-\tfrac{\chi}{\gamma})\big](\varphi-1)}$$
--   ((A.11), p. 32). A high-signal analyst forecasts high iff his posterior odds $\Pr(H|h)/\Pr(L|h)$ exceed $\Psi^h_i$ ((A.13)).
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Appendix A, (A.7), (A.11), p. 32

import Mathlib

namespace AnalystRanking.Revelation

/-- **`Ψʰ_i(σʰ, σˡ)`, (A.11).**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Appendix A, displays (A.7) and (A.11), p. 32:
`Ψʰ_i = (1 + [σʰ(1 − γ + χ/(1−γ)) + (1 − σˡ)(γ − χ/(1−γ))](φ − 1)) /
(φ − [σʰ(γ + χ/γ) + (1 − σˡ)(1 − γ − χ/γ)](φ − 1))`, with `χ = ργ(1 − γ)`.

**Formalization Note.** Transcribed as printed; `σ = (σʰ, σˡ)` is the other analyst's strategy.
For `σ ∈ [0, 1]²`, `0 < γ < 1`, `ρ ∈ [0, 1]` and `φ > 0` the denominator is positive. -/
noncomputable def psiH (γ ρ φ : ℝ) (σ : ℝ × ℝ) : ℝ :=
  let χ := ρ * γ * (1 - γ)
  (1 + (σ.1 * (1 - γ + χ / (1 - γ)) + (1 - σ.2) * (γ - χ / (1 - γ))) * (φ - 1)) /
    (φ - (σ.1 * (γ + χ / γ) + (1 - σ.2) * (1 - γ - χ / γ)) * (φ - 1))

end AnalystRanking.Revelation


