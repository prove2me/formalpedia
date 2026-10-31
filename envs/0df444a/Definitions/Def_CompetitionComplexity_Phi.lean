-- Prove2me | Definitions.Def_CompetitionComplexity_Phi
-- name    : CompetitionComplexity_Phi
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:27:43.494766+00:00
-- url     : https://prove2.me/theorems/5848f8e1-d31c-48bb-ac8e-6cd26d1232ef
-- title:
--   The threshold function $\phi(\varepsilon)=\int_0^1 \frac{dy}{y(1-\log y)+\varepsilon}$
-- statement:
--   For $\varepsilon>0$ the paper's threshold function is
--   $$
--   \phi(\varepsilon)=\int_0^1\frac{1}{y(1-\log y)+\varepsilon}\,dy .
--   $$
--   The integrand is positive and continuous on $(0,1]$, extends continuously to $y=0$ (since $y\log y\to0$), and is bounded by $1/\varepsilon$. Theorem 2 says that $\phi(\varepsilon)n$ buyers are exactly what dynamic pricing needs to reach a $1/(1+\varepsilon)$ fraction of the optimal auction's welfare with $n$ buyers, and that $\phi(\varepsilon)=\Theta(\log\log 1/\varepsilon)$.
--
--   **Formalization Note** The function is defined for every real $\varepsilon$ and used only for $\varepsilon>0$. Lean's convention $\log 0=0$ changes the integrand only at $y=0$, a null set.
-- source:
--   Brustle, Correa, Dütting, Verdugo, The Competition Complexity of Dynamic Pricing, accepted manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), doi:10.1287/moor.2022.0230, §1.3, p.3 (definition of ϕ); restated §5, p.21

import Mathlib

namespace CompetitionComplexity

/-- **The function `ϕ(ε) = ∫₀¹ 1/(y(1 − log y) + ε) dy`.**
Brustle, Correa, Dütting, Verdugo, *The Competition Complexity of Dynamic Pricing*, accepted
manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), §1.3, p.3 (restated §5, p.21).

**Formalization Note.** Defined for every real `ε` and used only for `ε > 0`, where the
integrand is continuous on `(0, 1]`, extends continuously to `y = 0`, and is bounded by `1/ε`.
Lean's `Real.log 0 = 0` changes the integrand only at the single point `y = 0`, a null set. -/
noncomputable def phi (ε : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..1, 1 / (y * (1 - Real.log y) + ε)

end CompetitionComplexity


