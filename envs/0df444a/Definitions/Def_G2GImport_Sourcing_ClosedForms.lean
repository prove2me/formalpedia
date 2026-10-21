-- Prove2me | Definitions.Def_G2GImport_Sourcing_ClosedForms
-- name    : G2GImport_Sourcing_ClosedForms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:46.031+00:00
-- url     : https://prove2.me/theorems/a31c2e76-52f7-4300-98fa-410ebdb4fc0d
-- title:
--   Proposition 3 payoff formulas and quadratic gap $D_2(l)$
-- statement:
--   The proof of Proposition 3 prints four formulas for the buyer's expected net utility and one supplier's expected profit in symmetric all-ad-hoc and all-forward negotiations with $l$ suppliers. Write them as $U_B^a(l)$, $U_B^f(l)$, $U_S^a(l)$ and $U_S^f(l)$. It also defines a quadratic $D_2(l)$ whose value determines the buyer's preference between the two regimes:
--   $$U_B^f(l)-U_B^a(l)=\frac{D_2(l)}{3(1-\gamma)l^2}.$$
--   The definitions retain the paper's displayed constants, radicals, and dependence on $c$, $\gamma$, and $l$; the subsequent theorem connects them to equilibrium payoffs.
--
--   **Formalization Note** The printed $n$ in the numerator of $U_S^f(l)$ is read as $l$, the all-forward supplier count. Real powers represent $c^{3/2}$ and $(c/(1-\gamma))^{3/2}$.
-- source:
--   Mu, Hu, Reddy & Gavirneni, Negotiating government-to-government food importing contracts: a Nash bargaining framework, accepted manuscript (MSOM, doi:10.1287/msom.2021.1027), PDF p. 14, proof of Proposition 3, displayed payoff formulas and D₂(l)

import Mathlib
import Definitions.Def_G2GImport_Sourcing_Model

namespace G2GImport.Sourcing

/-- The buyer's all-ad-hoc payoff printed in the proof of Proposition 3. -/
noncomputable def adHocBuyerClosed (P : Params) (l : ℝ) : ℝ :=
  (3 * P.c * l * (Real.sqrt (P.c / (1 - P.γ)) - 1)
    - 2 * P.c * Real.sqrt (P.c / (1 - P.γ))
    - l * (P.c / (1 - P.γ)) ^ ((3 : ℝ) / 2)
    + 3 * P.c + P.γ + 3 * l - 1) / (3 * l)

/-- The buyer's all-forward payoff printed in the proof of Proposition 3. -/
noncomputable def fwdBuyerClosed (P : Params) (l : ℝ) : ℝ :=
  (P.c ^ ((3 : ℝ) / 2) * (1 - P.γ + l * (3 * P.γ + 2 * l - 3))
    - 3 * P.c * (P.γ * (2 * l - 1) + (l - 1) ^ 2)
    + 3 * (P.γ - 1) * Real.sqrt P.c * (l - 1)
    + P.γ + 3 * l ^ 2 - 1) / (3 * l ^ 2)

/-- One supplier's all-ad-hoc payoff printed in the proof of Proposition 3. -/
noncomputable def adHocSupplierClosed (P : Params) (l : ℝ) : ℝ :=
  (P.c * (2 * Real.sqrt (P.c / (1 - P.γ)) - 3) + 1 - P.γ) / (3 * l ^ 2)

/-- One supplier's all-forward payoff printed in the proof of Proposition 3. The
printed `n` in its numerator is read as the total number `l` of forward suppliers. -/
noncomputable def fwdSupplierClosed (P : Params) (l : ℝ) : ℝ :=
  ((Real.sqrt P.c - 1) ^ 2 * (1 - P.γ) *
    (Real.sqrt P.c * (3 * l - 1) + 1)) / (3 * l ^ 3)

/-- The quadratic `D₂` displayed in the proof of Proposition 3. -/
noncomputable def D₂ (P : Params) (l : ℝ) : ℝ :=
  (2 * (1 - P.γ) + (3 * P.γ - 2) * Real.sqrt (1 / (1 - P.γ))) *
      P.c ^ ((3 : ℝ) / 2) * l ^ 2
    + (P.γ - 1) * P.c ^ ((3 : ℝ) / 2) *
      (-(-P.γ + 3 * (P.γ - 1) * l + 1))
    - 3 * Real.sqrt P.c * (P.γ - 1) ^ 2 * (l - 1)
    - P.c * ((P.γ - 1) * l *
      (2 * Real.sqrt (P.c / (1 - P.γ)) - 6 * P.γ + 3) +
      3 * (P.γ - 1) ^ 2)
    + (P.γ - 1) ^ 2 * (l - 1)

end G2GImport.Sourcing


