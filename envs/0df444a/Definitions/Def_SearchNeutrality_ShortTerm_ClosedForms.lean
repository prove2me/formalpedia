-- Prove2me | Definitions.Def_SearchNeutrality_ShortTerm_ClosedForms
-- name    : SearchNeutrality_ShortTerm_ClosedForms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T22:38:34.177974+00:00
-- url     : https://prove2.me/theorems/3197fbef-e4be-40ca-b25c-e06a0624dd34
-- title:
--   Appendix, pp. 42–46 — closed forms: α₁^NS, the NS interior prices, α₂^S, α₃^S, the (A2) deviation polynomial, and the consumer-surplus displays CS^NS, CS^S
-- statement:
--   Closed-form expressions of the Appendix of Zou and Zhou, in the model parameters $\rho_H,\rho_L,r$ and the popularity $\alpha$.
--
--   1. The bracket of case NS (p. 42, (A2); p. 43, (B)): $\;B(\alpha)=\alpha(\rho_H-\rho_L)(2+(3-r)\rho_H\rho_L)+\rho_L(2-(3-r)\rho_H^2)$.
--   2. The threshold (p. 42), with $s=\sqrt{2/(3-r)}$:
--   $$
--   \alpha_1^{NS}=\begin{cases}0,&\rho_H<s,\\[2pt] \dfrac{\rho_L((3-r)\rho_H^2-2)}{(\rho_H-\rho_L)(2+(3-r)\rho_H\rho_L)},&\rho_L<s\le\rho_H,\\[2pt] 1,&s\le\rho_L.\end{cases}
--   $$
--   3. The interior equilibrium prices without neutrality (p. 43):
--   $$
--   p_F^{NS}=\frac{(1-\alpha)^2\rho_L\rho_H^2(2+(1-\rho_L)\rho_H^2(1+r))+\alpha^2\rho_H\rho_L^2(2+(1-\rho_H)\rho_L^2(1+r))+\alpha(1-\alpha)\bigl(\rho_H^2\rho_L^2(\rho_H+\rho_L-2\rho_H\rho_L)(1+r)+2(\rho_H^3+\rho_L^3)\bigr)}{\rho_H\rho_L[(1-\alpha)\rho_H+\alpha\rho_L][(1-\alpha)(4-(1+r)\rho_L)\rho_H^2+\alpha(4-(1+r)\rho_H)\rho_L^2]},
--   $$
--   $$
--   p_T^{NS}=\frac{(1-\alpha)(\rho_L+2(1-\rho_L)\rho_H^2)+\alpha(\rho_H+2(1-\rho_H)\rho_L^2)}{(1-\alpha)\rho_H^2(4-(1+r)\rho_L)+\alpha\rho_L^2(4-(1+r)\rho_H)}.
--   $$
--   4. The thresholds with neutrality (p. 45): $\alpha_2^S=\dfrac{\rho_L^2(1-r\rho_H)}{\rho_H+\rho_L^2(1-r\rho_H)}$ and $\alpha_3^S=\dfrac{\rho_H}{\rho_H+\rho_L^2}$.
--   5. Seller $T$'s no-deviation polynomial of case (A2) (pp. 44–45): $\;2\alpha\rho_L^2-\rho_H[(2-3\rho_L^2)-\alpha(2-5\rho_L^2)]-\rho_H^2[r\rho_L^2+\alpha(1-r\rho_L^2)]$.
--   6. The consumer-surplus displays (pp. 44 and 46):
--   $$
--   CS^{NS}(p_F,p_T)=[\alpha\rho_H+(1-\alpha)\rho_L](1-p_F)+\tfrac{\alpha\rho_L^2}{2}[\rho_H(p_F-p_T)^2+(1-\rho_H)(1-p_T)^2]+\tfrac{(1-\alpha)\rho_H^2}{2}[\rho_L(p_F-p_T)^2+(1-\rho_L)(1-p_T)^2],
--   $$
--   $$
--   CS^{S}(p_F,p_T)=\alpha\Bigl[\rho_H(1-p_F)+\tfrac{(1-\rho_H)\rho_L^2(1-p_T)^2}{2}\Bigr]+(1-\alpha)\Bigl[\rho_H(1-p_T)+\tfrac{(1-\rho_H)\rho_L^2(1-p_F)^2}{2}\Bigr]+\tfrac{\rho_H\rho_L^2(p_F-p_T)^2}{2}\bigl[\mathbf 1(p_F\ge p_T)\alpha+\mathbf 1(p_F<p_T)(1-\alpha)\bigr].
--   $$
--
--   These are plain formulas; the theorems of the mission state what they describe (equilibrium prices, thresholds, surplus).
--
--   **Formalization Note** The printed (A2) condition has the factor $2+3\rho_H\rho_L$; the bracket uses $2+(3-r)\rho_H\rho_L$, the factor of the printed definition of $\alpha_{NS,1}$ two lines later and of case (B). The misprinted closed forms of the Appendix (the interior prices of (A1) and (B1), $\alpha_1^S$, $\alpha_4^S$) are deliberately not defined. Divisions are only ever used where the standing hypotheses make the denominators positive.
-- source:
--   Zou & Zhou, Self-Preferencing and Search Neutrality in Online Retail Platforms, authors' manuscript (Management Science, DOI 10.1287/mnsc.2022.01795), Appendix, p. 42 (α_{NS,1}, (A2)), p. 43 (display "Equilibrium prices without search neutrality"), p. 44 (CS^NS), pp. 44–45 ((A2)), p. 45 (α_2^S, α_3^S), p. 46 (CS^S)

import Mathlib
import Definitions.Def_SearchNeutrality_ShortTerm_Model

namespace SearchNeutrality.ShortTerm

/-! Closed-form objects of the Appendix of Zou & Zhou, *Self-Preferencing and Search Neutrality in
Online Retail Platforms*, authors' manuscript (Management Science, DOI 10.1287/mnsc.2022.01795),
pp. 42–46. Each is a plain formula in the model parameters `ρH ρL r` and the popularity `α`. -/

/-- The bracket of case NS (Appendix, p. 42, (A2), and p. 43, (B)):
`α(ρ_H − ρ_L)(2 + (3 − r)ρ_Hρ_L) + ρ_L(2 − (3 − r)ρ_H²)`. The printed (A2) has the factor
`2 + 3ρ_Hρ_L`; the factor `2 + (3 − r)ρ_Hρ_L` is the one of the definition of `α_{NS,1}` and of (B). -/
def nsBracket (ρH ρL r α : ℝ) : ℝ :=
  α * (ρH - ρL) * (2 + (3 - r) * ρH * ρL) + ρL * (2 - (3 - r) * ρH ^ 2)

/-- The threshold `α_1^{NS}` (Appendix, p. 42):
`𝟏(ρ_H < √(2/(3−r)))·0 + 𝟏(ρ_L < √(2/(3−r)) ≤ ρ_H)·ρ_L((3−r)ρ_H² − 2)/((ρ_H − ρ_L)(2 + (3−r)ρ_Hρ_L))
 + 𝟏(√(2/(3−r)) ≤ ρ_L)·1`. -/
noncomputable def alpha1NS (ρH ρL r : ℝ) : ℝ :=
  if ρH < Real.sqrt (2 / (3 - r)) then 0
  else if ρL < Real.sqrt (2 / (3 - r)) then
    ρL * ((3 - r) * ρH ^ 2 - 2) / ((ρH - ρL) * (2 + (3 - r) * ρH * ρL))
  else 1

/-- The interior equilibrium price `p_F^{NS*}` of case NS (Appendix, p. 43, display
"Equilibrium prices without search neutrality", case `α < α_1^{NS}`). -/
noncomputable def pFNS (ρH ρL r α : ℝ) : ℝ :=
  ((1 - α) ^ 2 * ρL * ρH ^ 2 * (2 + (1 - ρL) * ρH ^ 2 * (1 + r))
    + α ^ 2 * ρH * ρL ^ 2 * (2 + (1 - ρH) * ρL ^ 2 * (1 + r))
    + α * (1 - α) * (ρH ^ 2 * ρL ^ 2 * (ρH + ρL - 2 * ρH * ρL) * (1 + r) + 2 * (ρH ^ 3 + ρL ^ 3)))
  / (ρH * ρL * ((1 - α) * ρH + α * ρL)
      * ((1 - α) * (4 - (1 + r) * ρL) * ρH ^ 2 + α * (4 - (1 + r) * ρH) * ρL ^ 2))

/-- The interior equilibrium price `p_T^{NS*}` of case NS (Appendix, p. 43, same display). -/
noncomputable def pTNS (ρH ρL r α : ℝ) : ℝ :=
  ((1 - α) * (ρL + 2 * (1 - ρL) * ρH ^ 2) + α * (ρH + 2 * (1 - ρH) * ρL ^ 2))
  / ((1 - α) * ρH ^ 2 * (4 - (1 + r) * ρL) + α * ρL ^ 2 * (4 - (1 + r) * ρH))

/-- The threshold `α_2^S ≝ ρ_L²(1 − rρ_H)/(ρ_H + ρ_L²(1 − rρ_H))` (Appendix, p. 45, (A2)). -/
noncomputable def alpha2S (ρH ρL r : ℝ) : ℝ :=
  ρL ^ 2 * (1 - r * ρH) / (ρH + ρL ^ 2 * (1 - r * ρH))

/-- The threshold `α_3^S ≝ ρ_H/(ρ_H + ρ_L²)` (Appendix, p. 45, (B2)). -/
noncomputable def alpha3S (ρH ρL : ℝ) : ℝ :=
  ρH / (ρH + ρL ^ 2)

/-- Seller T's no-deviation polynomial of case (A2) (Appendix, pp. 44–45):
`2αρ_L² − ρ_H[(2 − 3ρ_L²) − α(2 − 5ρ_L²)] − ρ_H²[rρ_L² + α(1 − rρ_L²)]`. -/
def devPolyA2 (ρH ρL r α : ℝ) : ℝ :=
  2 * α * ρL ^ 2 - ρH * ((2 - 3 * ρL ^ 2) - α * (2 - 5 * ρL ^ 2))
    - ρH ^ 2 * (r * ρL ^ 2 + α * (1 - r * ρL ^ 2))

/-- The total consumer surplus display without search neutrality (Appendix, p. 44):
`[αρ_H + (1 − α)ρ_L](1 − p_F) + (αρ_L²/2)[ρ_H(p_F − p_T)² + (1 − ρ_H)(1 − p_T)²]
 + ((1 − α)ρ_H²/2)[ρ_L(p_F − p_T)² + (1 − ρ_L)(1 − p_T)²]`. -/
noncomputable def csNS (ρH ρL α pF pT : ℝ) : ℝ :=
  (α * ρH + (1 - α) * ρL) * (1 - pF)
    + α * ρL ^ 2 / 2 * (ρH * (pF - pT) ^ 2 + (1 - ρH) * (1 - pT) ^ 2)
    + (1 - α) * ρH ^ 2 / 2 * (ρL * (pF - pT) ^ 2 + (1 - ρL) * (1 - pT) ^ 2)

/-- The total consumer surplus display with search neutrality (Appendix, p. 46):
`α[ρ_H(1 − p_F) + (1 − ρ_H)ρ_L²(1 − p_T)²/2] + (1 − α)[ρ_H(1 − p_T) + (1 − ρ_H)ρ_L²(1 − p_F)²/2]
 + ρ_Hρ_L²(p_F − p_T)²/2·[𝟏(p_F ≥ p_T)·α + 𝟏(p_F < p_T)·(1 − α)]`. -/
noncomputable def csS (ρH ρL α pF pT : ℝ) : ℝ :=
  α * (ρH * (1 - pF) + (1 - ρH) * ρL ^ 2 * (1 - pT) ^ 2 / 2)
    + (1 - α) * (ρH * (1 - pT) + (1 - ρH) * ρL ^ 2 * (1 - pF) ^ 2 / 2)
    + ρH * ρL ^ 2 * (pF - pT) ^ 2 / 2 * (if pT ≤ pF then α else 1 - α)

end SearchNeutrality.ShortTerm


