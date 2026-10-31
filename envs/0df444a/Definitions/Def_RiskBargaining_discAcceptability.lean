-- Prove2me | Definitions.Def_RiskBargaining_discAcceptability
-- name    : RiskBargaining_discAcceptability
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:25:18.127492+00:00
-- url     : https://prove2.me/theorems/f36570af-e8b8-406a-a2f4-c9ed43159630
-- title:
--   The functionals $\mathcal A_\pm$ of the counterexample to Proposition 1
-- statement:
--   Let $Y\in L^p$ on the three-point uniform space have values $x_1,x_2,x_3$. Put $a=x_1-x_2$, $b=x_1+x_2-2x_3$, $\rho=1/20$. For $s\in\mathbb R$,
--   $$
--   \mathcal A_s(Y)=\frac{x_1+x_2+x_3}{3}+s\,\rho\sqrt3\,a-\rho\sqrt{3a^2+b^2}.
--   $$
--   The choices $s=1$ and $s=-1$ give the functionals $\mathcal A_+$ and $\mathcal A_-$ of the counterexample to Proposition 1.
--
--   **Formalization Note** The values are read from the `Lp` representative. They do not depend on the representative because each point has positive mass.
-- source:
--   Gutjahr, Kovacevic, Wozabal, Risk-Averse Bargaining in a Stochastic Optimization Context, manuscript, Appendix A.1, p.34 (the functionals are not in the paper)

import Mathlib
import Definitions.Def_RiskBargaining_uniformThree

open MeasureTheory
open scoped ENNReal

namespace RiskBargaining

/-- **The functionals `𝒜_±` of the counterexample to Proposition 1**, with `ρ = 1/20`.
For `Y ∈ L^p(Fin 3)` with values `x₁, x₂, x₃`, and `a = x₁ - x₂`, `b = x₁ + x₂ - 2 x₃`,
`discAcceptability s Y = E[Y] + s ρ √3 a - ρ √(3 a² + b²)`; `s = 1` gives `𝒜_+` and `s = -1` gives `𝒜_-`.

**Formalization Note.** The values `Y 0, Y 1, Y 2` are those of the `Lp` representative. They do not
depend on it, because each point has positive mass. Not in the paper: Gutjahr, Kovacevic, Wozabal, *Risk-Averse Bargaining in a Stochastic Optimization Context*, manuscript, Appendix A.1, p.34,
is the step that the counterexample refutes. -/
noncomputable def discAcceptability (p : ℝ≥0∞) [Fact (1 ≤ p)] (s : ℝ)
    (Y : Lp ℝ p uniformThree) : ℝ :=
  (Y 0 + Y 1 + Y 2) / 3 + s * (1 / 20) * Real.sqrt 3 * (Y 0 - Y 1) -
    (1 / 20) * Real.sqrt (3 * (Y 0 - Y 1) ^ 2 + (Y 0 + Y 1 - 2 * Y 2) ^ 2)

end RiskBargaining


