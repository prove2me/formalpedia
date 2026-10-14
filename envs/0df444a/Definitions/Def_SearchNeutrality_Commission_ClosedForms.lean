-- Prove2me | Definitions.Def_SearchNeutrality_Commission_ClosedForms
-- name    : SearchNeutrality_Commission_ClosedForms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T22:38:28.19358+00:00
-- url     : https://prove2.me/theorems/cc9173fc-01a1-490d-a31c-5fc6a5023d5c
-- title:
--   Appendix, pp. 43–44 — closed-form equilibrium prices p_F^{NS*}, p_T^{NS*} and consumer surplus CS^{NS} without search neutrality
-- statement:
--   Closed forms of the Appendix (pp. 43–44) for the scenario without search neutrality in which product $F$ is prominent for all consumers.
--
--   1. The interior equilibrium prices (display "Equilibrium prices without search neutrality", p. 43):
--   $$p_F^{NS*}=\frac{(1-\alpha)^2\rho_L\rho_H^2\bigl(2+(1-\rho_L)\rho_H^2(1+r)\bigr)+\alpha^2\rho_H\rho_L^2\bigl(2+(1-\rho_H)\rho_L^2(1+r)\bigr)+\alpha(1-\alpha)\bigl(\rho_H^2\rho_L^2(\rho_H+\rho_L-2\rho_H\rho_L)(1+r)+2(\rho_H^3+\rho_L^3)\bigr)}{\rho_H\rho_L[(1-\alpha)\rho_H+\alpha\rho_L]\,[(1-\alpha)(4-(1+r)\rho_L)\rho_H^2+\alpha(4-(1+r)\rho_H)\rho_L^2]},$$
--   $$p_T^{NS*}=\frac{(1-\alpha)(\rho_L+2(1-\rho_L)\rho_H^2)+\alpha(\rho_H+2(1-\rho_H)\rho_L^2)}{(1-\alpha)\rho_H^2(4-(1+r)\rho_L)+\alpha\rho_L^2(4-(1+r)\rho_H)}.$$
--   2. The total consumer surplus display (p. 44), as a function of prices $p_F\ge p_T$:
--   $$CS^{NS}(p_F,p_T)=[\alpha\rho_H+(1-\alpha)\rho_L](1-p_F)+\frac{\alpha\rho_L^2}{2}\bigl[\rho_H(p_F-p_T)^2+(1-\rho_H)(1-p_T)^2\bigr]+\frac{(1-\alpha)\rho_H^2}{2}\bigl[\rho_L(p_F-p_T)^2+(1-\rho_L)(1-p_T)^2\bigr].$$
--
--   These are the formulas the milestones of this mission compare equilibria and surplus against. They are only definitions: the claims that they are the equilibrium prices and the surplus are separate theorems.
--
--   **Formalization Note** The denominators are positive under $0<\rho_L<\rho_H<1$, $0\le r\le 1$, $\alpha\in[0,1]$, so Lean's convention $x/0=0$ is never reached on the parameter range used.
-- source:
--   Zou & Zhou, Self-Preferencing and Search Neutrality in Online Retail Platforms, authors' manuscript (Management Science, DOI 10.1287/mnsc.2022.01795), p. 43, display "Equilibrium prices without search neutrality"; p. 44, total consumer surplus CS^{NS}

import Mathlib
import Definitions.Def_SearchNeutrality_Commission_Model

namespace SearchNeutrality.Commission

/-! Zou & Zhou, authors' manuscript (Management Science, DOI 10.1287/mnsc.2022.01795),
Appendix, pp. 43–44: closed forms of the scenario without search neutrality (F prominent for
all consumers). -/

/-- The interior equilibrium price `p_F^{NS*}` of the platform (Appendix, p. 43, display
"Equilibrium prices without search neutrality", case `α < α_1^{NS}`). -/
noncomputable def pFNS (ρH ρL r α : ℝ) : ℝ :=
  ((1 - α) ^ 2 * ρL * ρH ^ 2 * (2 + (1 - ρL) * ρH ^ 2 * (1 + r))
      + α ^ 2 * ρH * ρL ^ 2 * (2 + (1 - ρH) * ρL ^ 2 * (1 + r))
      + α * (1 - α) * (ρH ^ 2 * ρL ^ 2 * (ρH + ρL - 2 * ρH * ρL) * (1 + r)
          + 2 * (ρH ^ 3 + ρL ^ 3)))
    / (ρH * ρL * ((1 - α) * ρH + α * ρL)
        * ((1 - α) * (4 - (1 + r) * ρL) * ρH ^ 2 + α * (4 - (1 + r) * ρH) * ρL ^ 2))

/-- The interior equilibrium price `p_T^{NS*}` of the third-party seller (Appendix, p. 43). -/
noncomputable def pTNS (ρH ρL r α : ℝ) : ℝ :=
  ((1 - α) * (ρL + 2 * (1 - ρL) * ρH ^ 2) + α * (ρH + 2 * (1 - ρH) * ρL ^ 2))
    / ((1 - α) * ρH ^ 2 * (4 - (1 + r) * ρL) + α * ρL ^ 2 * (4 - (1 + r) * ρH))

/-- The total consumer surplus display `CS^{NS}` (Appendix, p. 44) as a function of the prices,
for `F` prominent for all consumers and `p_F ≥ p_T`. -/
noncomputable def csNS (ρH ρL α pF pT : ℝ) : ℝ :=
  (α * ρH + (1 - α) * ρL) * (1 - pF)
    + α * ρL ^ 2 / 2 * (ρH * (pF - pT) ^ 2 + (1 - ρH) * (1 - pT) ^ 2)
    + (1 - α) * ρH ^ 2 / 2 * (ρL * (pF - pT) ^ 2 + (1 - ρL) * (1 - pT) ^ 2)

end SearchNeutrality.Commission


