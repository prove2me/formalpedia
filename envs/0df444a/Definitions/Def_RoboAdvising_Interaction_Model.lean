-- Prove2me | Definitions.Def_RoboAdvising_Interaction_Model
-- name    : RoboAdvising_Interaction_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:04.296082+00:00
-- url     : https://prove2.me/theorems/7384763c-23da-4fbc-b6e7-a95ac533c9bd
-- title:
--   Proposition 5.1(i), p. 21 — the approximate personalization measure R̃(φ, β), its standing ranges, the minimizer predicate, and f, g of the proof (p. 46)
-- statement:
--   The objects of Proposition 5.1 of Capponi, Ólafsson and Zariphopoulou, *Personalized Robo-Advising*.
--
--   **Parameters.** A parameter set consists of four real numbers: $\sigma_0 = \sigma(Y_0)$, the volatility of the market return in the initial economic state; $p_\epsilon$, the probability of an idiosyncratic risk-aversion shock in a period; $\sigma_\epsilon$, the volatility of such a shock; and $\beta$, the strength of the client's behavioral bias. The **standing ranges** of the paper are
--   $$\sigma_0 > 0,\qquad \sigma_\epsilon > 0,\qquad p_\epsilon \in [0,1],\qquad \beta \ge 0 .$$
--
--   **The approximate personalization measure.** For a time $\phi$ between consecutive client interactions,
--   $$\widetilde{\mathcal R}(\phi,\beta) := \sqrt{\frac{2}{\pi}}\left(\frac{\beta\sigma_0}{\sqrt{\phi}}\Big(1-\frac{\phi-1}{2}p_\epsilon\Big) + \sqrt{\frac{\beta^2\sigma_0^2}{\phi}+\sigma_\epsilon^2}\;\frac{\phi-1}{2}p_\epsilon\right).$$
--   A lower value means a portfolio that tracks the client's true risk aversion more closely. A number $\phi$ is an **optimal interaction time** if $\phi \ge 1$ and $\widetilde{\mathcal R}(\phi,\beta) \le \widetilde{\mathcal R}(\psi,\beta)$ for every $\psi \ge 1$.
--
--   **Auxiliary functions of the proof.** The bracket $f(\phi) = \sqrt{\pi/2}\,\widetilde{\mathcal R}(\phi,\beta)$, that is
--   $$f(\phi) = \frac{\beta\sigma_0}{\sqrt{\phi}}\Big(1-\frac{\phi-1}{2}p_\epsilon\Big) + \sqrt{\frac{\beta^2\sigma_0^2}{\phi}+\sigma_\epsilon^2}\;\frac{\phi-1}{2}p_\epsilon,$$
--   and, for $\beta > 0$ and $p_\epsilon > 0$,
--   $$g(\phi) = -\frac{\sqrt{\phi}}{p_\epsilon} + \frac12\Big(1-\frac{1}{\sqrt{1+\frac{\sigma_\epsilon^2\phi}{\beta^2\sigma_0^2}}}\Big)\sqrt{\phi}(\phi-1) + \Big(\sqrt{1+\frac{\sigma_\epsilon^2\phi}{\beta^2\sigma_0^2}}-1\Big)\phi^{3/2},$$
--   which satisfies $f'(\phi) = \tfrac12 \frac{\beta\sigma_0 p_\epsilon}{\phi^2} g(\phi)$.
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** All quantities are real. The time between interactions $\phi$ is a real variable (the model of §5.1 uses integer $\phi$, but Proposition 5.1 differentiates in $\phi$ and places $\phi_0 \in [1,\infty)$); statements restrict it to $\phi \ge 1$, or $\phi > 0$ for derivatives, so the conventions $\sqrt{x} = 0$ for $x < 0$ and $x/0 = 0$ never enter. `Rtilde P φ` takes $\phi$ as its last argument (the page writes both $\widetilde{\mathcal R}(\phi,\beta)$ and $\widetilde{\mathcal R}(\beta,\phi)$). The page's display on p. 46 writes $f := \sqrt{2/\pi}\,\widetilde{\mathcal R}$; the right-hand side it gives is the bracket, which equals $\sqrt{\pi/2}\,\widetilde{\mathcal R}$, and that bracket is what `fAux` is. $\phi^{3/2}$ is written $\phi\sqrt\phi$. `gAux` divides by $p_\epsilon$ and $\beta^2\sigma_0^2$ and is used only when $\beta > 0$ and $p_\epsilon > 0$.
-- source:
--   Capponi, Ólafsson, Zariphopoulou, Personalized Robo-Advising: Enhancing Investment through Client Interaction, arXiv:1911.01391v2, pp. 8, 21, 22, 46: σ(y) > 0 (§3.1, p. 8), ranges of pϵ, σϵ, β and Proposition 5.1(i) display of R̃ (p. 21), arg min over φ ≥ 1 (Proposition 5.1(ii), p. 22), f and g (proof of Proposition 5.1, p. 46)

import Mathlib

namespace RoboAdvising.Interaction

/-- The parameters of Proposition 5.1 (Capponi–Ólafsson–Zariphopoulou, arXiv:1911.01391v2, p. 21):
`sig0` is σ0 = σ(Y0), the return volatility in the initial economic state; `pe` is pϵ, the
probability of an idiosyncratic risk-aversion shock; `se` is σϵ, the shock volatility; `β` is the
client's behavioral-bias coefficient. -/
structure Params where
  /-- σ0 = σ(Y0) -/
  sig0 : ℝ
  /-- pϵ -/
  pe : ℝ
  /-- σϵ -/
  se : ℝ
  /-- β -/
  β : ℝ

/-- The standing ranges of the parameters: σ0 > 0 (p. 8, `0 < σ²(y) < ∞`), σϵ > 0 (p. 21),
pϵ ∈ [0, 1] (p. 21) and β ≥ 0 (p. 21). -/
def Params.Standing (P : Params) : Prop :=
  0 < P.sig0 ∧ 0 < P.se ∧ 0 ≤ P.pe ∧ P.pe ≤ 1 ∧ 0 ≤ P.β

/-- The approximate personalization measure of Proposition 5.1(i), p. 21:
R̃(φ, β) = √(2/π) ( (βσ0/√φ)(1 − ((φ−1)/2) pϵ) + √(β²σ0²/φ + σϵ²) ((φ−1)/2) pϵ ).
The time between interactions `φ` is the last argument. -/
noncomputable def Rtilde (P : Params) (φ : ℝ) : ℝ :=
  Real.sqrt (2 / Real.pi) *
    (P.β * P.sig0 / Real.sqrt φ * (1 - (φ - 1) / 2 * P.pe)
      + Real.sqrt (P.β ^ 2 * P.sig0 ^ 2 / φ + P.se ^ 2) * ((φ - 1) / 2) * P.pe)

/-- `φ` is a minimizer of R̃ over the interaction times `φ ≥ 1` (the `arg min_{φ ≥ 1}` of
Proposition 5.1(ii), p. 22). -/
def IsOptInteraction (P : Params) (φ : ℝ) : Prop :=
  1 ≤ φ ∧ IsMinOn (Rtilde P) (Set.Ici 1) φ

/-- The function `f` of the proof of Proposition 5.1, p. 46: the bracket of R̃, i.e.
`f = √(π/2) R̃`. -/
noncomputable def fAux (P : Params) (φ : ℝ) : ℝ :=
  P.β * P.sig0 / Real.sqrt φ * (1 - (φ - 1) / 2 * P.pe)
    + Real.sqrt (P.β ^ 2 * P.sig0 ^ 2 / φ + P.se ^ 2) * ((φ - 1) / 2) * P.pe

/-- The function `g` of the proof of Proposition 5.1, p. 46, defined by
`f′(φ) = ½ (βσ0pϵ/φ²) g(φ)`:
g(φ) = −√φ/pϵ + ½(1 − 1/√(1 + σϵ²φ/(β²σ0²))) √φ(φ − 1) + (√(1 + σϵ²φ/(β²σ0²)) − 1) φ^{3/2}.
It is only meaningful for β > 0 and pϵ > 0. -/
noncomputable def gAux (P : Params) (φ : ℝ) : ℝ :=
  -(Real.sqrt φ / P.pe)
    + 1 / 2 * (1 - 1 / Real.sqrt (1 + P.se ^ 2 * φ / (P.β ^ 2 * P.sig0 ^ 2)))
        * Real.sqrt φ * (φ - 1)
    + (Real.sqrt (1 + P.se ^ 2 * φ / (P.β ^ 2 * P.sig0 ^ 2)) - 1) * (φ * Real.sqrt φ)

end RoboAdvising.Interaction


