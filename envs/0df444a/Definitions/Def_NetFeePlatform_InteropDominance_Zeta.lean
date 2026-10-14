-- Prove2me | Definitions.Def_NetFeePlatform_InteropDominance_Zeta
-- name    : NetFeePlatform_InteropDominance_Zeta
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T10:12:10.042511+00:00
-- url     : https://prove2.me/theorems/eedc0632-76e8-4bc2-a049-c42118982c14
-- title:
--   Appendix E.2, proof of Proposition 6, p. 51 — the characterization function ζ(n¹; λ) of duopoly equilibrium shares
-- statement:
--   For a network-interaction value $\gamma$ and a degree of interoperability $\lambda$, the function $\zeta(\cdot\,;\lambda)$ of a market share $n\in(0,1)$ is
--
--   $$\zeta(n;\lambda)=\ln\frac{n}{1-n}+\frac{1}{1-n}-\frac1n-2\gamma(1-\lambda)(2n-1).$$
--
--   In a Logit duopoly without outside option, the market shares of the duopoly equilibria under interoperability $\lambda$ are exactly the zeros of $\zeta(\cdot\,;\lambda)$ (when the first-order condition is sufficient). The proof of Proposition 6 compares $\zeta$ at two levels of interoperability.
--
--   **Formalization Note** The function is defined for every real $n$ with Lean's total operations ($\ln$ of a non-positive number and division by zero return $0$); it is only ever used for $n\in(0,1)$, where every term is the paper's.
-- source:
--   Ekmekci, White & Wu, Platform Competition and Interoperability: The Net Fee Model, accepted working-paper version (December 12, 2024), p. 51, Appendix E.2, proof of Proposition 6

import Mathlib
import Definitions.Def_NetFeePlatform_Competition_Setting

namespace NetFeePlatform.InteropDominance

/-- The characterization function of the proof of Proposition 6 (Appendix E.2, p. 51):
ζ(n¹; λ) = ln(n¹/(1 − n¹)) + 1/(1 − n¹) − 1/n¹ − 2γ(1 − λ)(2n¹ − 1). -/
noncomputable def zeta (γ lam n : ℝ) : ℝ :=
  Real.log (n / (1 - n)) + 1 / (1 - n) - 1 / n - 2 * γ * (1 - lam) * (2 * n - 1)

end NetFeePlatform.InteropDominance


