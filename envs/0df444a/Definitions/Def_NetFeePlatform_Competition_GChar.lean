-- Prove2me | Definitions.Def_NetFeePlatform_Competition_GChar
-- name    : NetFeePlatform_Competition_GChar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T08:30:55.172715+00:00
-- url     : https://prove2.me/theorems/180c1f92-f791-4386-996d-a93664f6228e
-- title:
--   Proof of Proposition 4, p. 49 — the characterization function g(n; J) of equilibria with one dominant and J − 1 equal small platforms
-- statement:
--   The characterization function of the proof of Proposition 4.
--
--   Consider $J\ge2$ platforms of which one is dominant and the other $J-1$ are equally sized. Let $n$ be the **total** share of the $J-1$ small platforms, so the dominant platform has share $n^1=1-n$ and each small platform has share $n^2=n/(J-1)$. For a common interaction value $\gamma$ define, for $0<n<1$,
--   $$g(n;J)=\ln n-\ln(J-1)-\ln(1-n)+\frac{1}{1-\frac{n}{J-1}}-2\gamma\frac{n}{J-1}-\Big(\frac1n-2\gamma(1-n)\Big).$$
--
--   The first three terms are $\ln(n^2/n^1)$; the last terms are the difference $t^2-t^1$ of the two Logit pricing formulas. A zero of $g(\cdot;J)$ therefore says that the share ratio produced by the two pricing formulas equals the ratio assumed, which is how the paper locates equilibria with one dominant platform.
--
--   **Formalization Note** $J$ is a natural number cast to the reals. Outside $0<n<1$ the Lean function takes junk values (`Real.log` of a nonpositive number is $0$), so every statement about it assumes $0<n<1$.
-- source:
--   Ekmekci, White & Wu, Platform Competition and Interoperability: The Net Fee Model, accepted working-paper version (December 12, 2024), p. 49, Appendix E.2, proof of Proposition 4

import Mathlib
import Definitions.Def_NetFeePlatform_Competition_Setting

namespace NetFeePlatform.Competition

/-- The characterization function g(n; J) of the proof of Proposition 4 (p. 49). Here `n` is the
total share of the J − 1 equal small platforms: the dominant platform has share 1 − n and each
small platform n/(J − 1).
g(n; J) = ln n − ln(J − 1) − ln(1 − n) + 1/(1 − n/(J − 1)) − 2γ n/(J − 1) − (1/n − 2γ(1 − n)). -/
noncomputable def gChar (γ : ℝ) (J : ℕ) (n : ℝ) : ℝ :=
  Real.log n - Real.log ((J : ℝ) - 1) - Real.log (1 - n) + 1 / (1 - n / ((J : ℝ) - 1))
    - 2 * γ * (n / ((J : ℝ) - 1)) - (1 / n - 2 * γ * (1 - n))

end NetFeePlatform.Competition


