-- Prove2me | Definitions.Def_AnalystRanking_Revelation_psiL
-- name    : AnalystRanking_Revelation_psiL
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:38:03.933053+00:00
-- url     : https://prove2.me/theorems/051d16af-a923-425a-9cd6-db8f8c69c481
-- title:
--   $\Psi^l_i(\sigma^h,\sigma^l)$, (A.12)
-- statement:
--   With $\chi=\rho\gamma(1-\gamma)$ and the other analyst's strategy $(\sigma^h,\sigma^l)$,
--   $$\Psi^l_i=\frac{1+\big[\sigma^h(1-\gamma-\tfrac{\chi}{\gamma})+(1-\sigma^l)(\gamma+\tfrac{\chi}{\gamma})\big](\varphi-1)}{\varphi-\big[\sigma^h(\gamma-\tfrac{\chi}{1-\gamma})+(1-\sigma^l)(1-\gamma+\tfrac{\chi}{1-\gamma})\big](\varphi-1)}$$
--   ((A.12), p. 32). A low-signal analyst forecasts low iff $\Psi^l_i$ exceeds his posterior odds $\Pr(H|l)/\Pr(L|l)$ ((A.14)).
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Appendix A, (A.7), (A.12), p. 32

import Mathlib

namespace AnalystRanking.Revelation

/-- **`Ψˡ_i(σʰ, σˡ)`, (A.12).**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Appendix A, displays (A.7) and (A.12), p. 32:
`Ψˡ_i = (1 + [σʰ(1 − γ − χ/γ) + (1 − σˡ)(γ + χ/γ)](φ − 1)) /
(φ − [σʰ(γ − χ/(1−γ)) + (1 − σˡ)(1 − γ + χ/(1−γ))](φ − 1))`, with `χ = ργ(1 − γ)`.

**Formalization Note.** Transcribed as printed; `σ = (σʰ, σˡ)` is the other analyst's strategy.
For `σ ∈ [0, 1]²`, `0 < γ < 1`, `ρ ∈ [0, 1]` and `φ > 0` the denominator is positive. -/
noncomputable def psiL (γ ρ φ : ℝ) (σ : ℝ × ℝ) : ℝ :=
  let χ := ρ * γ * (1 - γ)
  (1 + (σ.1 * (1 - γ - χ / γ) + (1 - σ.2) * (γ + χ / γ)) * (φ - 1)) /
    (φ - (σ.1 * (γ - χ / (1 - γ)) + (1 - σ.2) * (1 - γ + χ / (1 - γ))) * (φ - 1))

end AnalystRanking.Revelation


