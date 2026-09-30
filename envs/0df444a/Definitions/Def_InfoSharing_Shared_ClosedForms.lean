-- Prove2me | Definitions.Def_InfoSharing_Shared_ClosedForms
-- name    : InfoSharing_Shared_ClosedForms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T05:53:46.874171+00:00
-- url     : https://prove2.me/theorems/e2b902a6-bdc4-4732-a6c7-3854f679ab11
-- title:
--   Closed-form equilibrium prices and ex ante profits, §4.1–4.2
-- statement:
--   The explicit quantities of Lemma 1 and §4.2, as functions of $a, b, c, \phi, \sigma, \beta$. The deterministic prices are
--
--   $$\bar w = \frac{(1+(1+\phi)c)a + (1+\phi)b}{2+\phi+(1+\phi)c}, \qquad \bar p = \frac{(3+\phi+2(1+\phi)c)a + (1+\phi)b}{2(2+\phi+(1+\phi)c)}.$$
--
--   The signal coefficients are $\alpha_w(0) = \alpha_w^U(1) = 0$, $\alpha_w^I(1) = \frac{1+(1+\phi)c}{(1+\phi)(2+(1+\phi)c)}\beta$, $\alpha_w(2) = \frac{1+(1+\phi)c}{2+\phi+(1+\phi)c}\beta$, $\alpha_p(0) = \alpha_p^U(1) = \beta/2$, $\alpha_p^I(1) = \frac{3+2\phi+(1+\phi)(2+\phi)c}{2(1+\phi)(2+(1+\phi)c)}\beta$ and $\alpha_p(2) = \frac{3+\phi+2(1+\phi)c}{2(2+\phi+(1+\phi)c)}\beta$.
--
--   The deterministic profits are $\bar\pi_M = \frac{(1+\phi)(2+(1+\phi)c)(a-b)^2}{4(2+\phi+(1+\phi)c)^2}$ and $\bar\pi_R = \frac{(1+\phi)^2(a-b)^2}{2(2+\phi+(1+\phi)c)^2}$. The seven ex ante profits are
--
--   $$\pi_M(0) = \bar\pi_M - \tfrac{c\beta\sigma^2}{4} - c(1-\beta)\sigma^2,\quad \pi_M^U(1) = \bar\pi_M - \tfrac{c}{4}\Big[\tfrac{2+3\phi+(1+\phi)(1+2\phi)c}{(1+\phi)(2+(1+\phi)c)}\Big]^2\beta\sigma^2 - c(1-\beta)\sigma^2,$$
--
--   $$\pi_M^I(1) = \bar\pi_M + \tfrac{\beta\sigma^2}{4(1+\phi)(2+(1+\phi)c)} - c(1-\beta)\sigma^2,\quad \pi_M(2) = \bar\pi_M + \tfrac{(1+\phi)(2+(1+\phi)c)}{4(2+\phi+(1+\phi)c)^2}\beta\sigma^2 - c(1-\beta)\sigma^2,$$
--
--   $$\pi_R(0) = \bar\pi_R + \tfrac{\beta\sigma^2}{2},\quad \pi_R(1) = \bar\pi_R + \Big[\tfrac{1+2\phi}{1+\phi} + \tfrac{1}{(1+\phi)(2+(1+\phi)c)^2}\Big]\tfrac{\beta\sigma^2}{4},\quad \pi_R(2) = \bar\pi_R + \tfrac{(1+\phi)^2}{2(2+\phi+(1+\phi)c)^2}\beta\sigma^2.$$
--
--   These are named constants only; the milestones assert that the equilibrium quantities equal them.
--
--   **Formalization Note.** $\alpha_w$ and $\alpha_p$ are written as functions of the status profile and of the manufacturer, selecting the case by $n$ and the manufacturer's own status.
--
--   **Formalization Note (production economy).** In the production economy $c = -c_e$, and the Assumption $c_e < 2/(1+\phi)$ makes $2+(1+\phi)c > 0$ and $2+\phi+(1+\phi)c > 0$.
--
--   This is a shared definition of the series, reviewed once for both missions: `01-diseconomy-sequential` (production diseconomy, §5; Shang, Ha & Tong 2016, pp. 251–252, Lemma 1 and §4.2) and `02-economy-sequential` (production economy, §6; pp. 251–252, Lemma 1 and §4.2 (with $c = -c_e$)). The cost parameter $c$ is a plain real; the missions differ only in the hypotheses their theorems put on it: $c > 0$ in the first, $c = -c_e$ with $0 < c_e < 2/(1+\phi)$ in the second.
-- source:
--   Shang, Ha & Tong, Information Sharing in a Supply Chain with a Common Retailer, Management Sci. 62(1) 2016, p. 251 (w̄, p̄, Lemma 1); p. 252, §4.2

import Mathlib
import Definitions.Def_InfoSharing_Shared_Status

namespace InfoSharing.Shared

/-- `w̄`, the deterministic (`σ = 0`) equilibrium wholesale price (p. 251):
`[(1 + (1+φ)c)a + (1+φ)b] / (2 + φ + (1+φ)c)`. -/
noncomputable def wbar (a b c φ : ℝ) : ℝ :=
  ((1 + (1 + φ) * c) * a + (1 + φ) * b) / (2 + φ + (1 + φ) * c)

/-- `p̄`, the deterministic equilibrium retail price (p. 251):
`[(3 + φ + 2(1+φ)c)a + (1+φ)b] / [2(2 + φ + (1+φ)c)]`. -/
noncomputable def pbar (a b c φ : ℝ) : ℝ :=
  ((3 + φ + 2 * (1 + φ) * c) * a + (1 + φ) * b) / (2 * (2 + φ + (1 + φ) * c))

/-- Lemma 1's wholesale-price signal coefficient of manufacturer `i` under profile `X`:
`α_w(0) = α_w^U(1) = 0`, `α_w^I(1) = (1+(1+φ)c)β/[(1+φ)(2+(1+φ)c)]`,
`α_w(2) = (1+(1+φ)c)β/(2+φ+(1+φ)c)` (p. 251). -/
noncomputable def alphaW (c φ β : ℝ) (X : Fin 2 → Status) (i : Fin 2) : ℝ :=
  if numInformed X = 2 then (1 + (1 + φ) * c) / (2 + φ + (1 + φ) * c) * β
  else if numInformed X = 1 ∧ X i = Status.informed then
    (1 + (1 + φ) * c) / ((1 + φ) * (2 + (1 + φ) * c)) * β
  else 0

/-- Lemma 1's retail-price signal coefficient of product `i` under profile `X`:
`α_p(0) = α_p^U(1) = β/2`, `α_p^I(1) = (3+2φ+(1+φ)(2+φ)c)β/[2(1+φ)(2+(1+φ)c)]`,
`α_p(2) = (3+φ+2(1+φ)c)β/[2(2+φ+(1+φ)c)]` (p. 251). -/
noncomputable def alphaP (c φ β : ℝ) (X : Fin 2 → Status) (i : Fin 2) : ℝ :=
  if numInformed X = 2 then (3 + φ + 2 * (1 + φ) * c) / (2 * (2 + φ + (1 + φ) * c)) * β
  else if numInformed X = 1 ∧ X i = Status.informed then
    (3 + 2 * φ + (1 + φ) * (2 + φ) * c) / (2 * (1 + φ) * (2 + (1 + φ) * c)) * β
  else β / 2

/-- `π̄_M`, a manufacturer's profit in the deterministic model (p. 252):
`(1+φ)(2+(1+φ)c)(a−b)² / [4(2+φ+(1+φ)c)²]`. -/
noncomputable def piMbar (a b c φ : ℝ) : ℝ :=
  (1 + φ) * (2 + (1 + φ) * c) * (a - b) ^ 2 / (4 * (2 + φ + (1 + φ) * c) ^ 2)

/-- `π̄_R`, the retailer's profit in the deterministic model (p. 252):
`(1+φ)²(a−b)² / [2(2+φ+(1+φ)c)²]`. -/
noncomputable def piRbar (a b c φ : ℝ) : ℝ :=
  (1 + φ) ^ 2 * (a - b) ^ 2 / (2 * (2 + φ + (1 + φ) * c) ^ 2)

/-- `π_M(0) = π̄_M − cβσ²/4 − c(1−β)σ²` (p. 252). -/
noncomputable def piM0 (a b c φ σ β : ℝ) : ℝ :=
  piMbar a b c φ - c * β * σ ^ 2 / 4 - c * (1 - β) * σ ^ 2

/-- `π_M^U(1) = π̄_M − (c/4)[(2+3φ+(1+φ)(1+2φ)c)/((1+φ)(2+(1+φ)c))]² βσ² − c(1−β)σ²`
(p. 252). -/
noncomputable def piMU1 (a b c φ σ β : ℝ) : ℝ :=
  piMbar a b c φ
    - c / 4 * ((2 + 3 * φ + (1 + φ) * (1 + 2 * φ) * c) / ((1 + φ) * (2 + (1 + φ) * c))) ^ 2
      * β * σ ^ 2
    - c * (1 - β) * σ ^ 2

/-- `π_M^I(1) = π̄_M + βσ²/[4(1+φ)(2+(1+φ)c)] − c(1−β)σ²` (p. 252). -/
noncomputable def piMI1 (a b c φ σ β : ℝ) : ℝ :=
  piMbar a b c φ + 1 / (4 * (1 + φ) * (2 + (1 + φ) * c)) * β * σ ^ 2
    - c * (1 - β) * σ ^ 2

/-- `π_M(2) = π̄_M + (1+φ)(2+(1+φ)c)βσ²/[4(2+φ+(1+φ)c)²] − c(1−β)σ²` (p. 252). -/
noncomputable def piM2 (a b c φ σ β : ℝ) : ℝ :=
  piMbar a b c φ
    + (1 + φ) * (2 + (1 + φ) * c) / (4 * (2 + φ + (1 + φ) * c) ^ 2) * β * σ ^ 2
    - c * (1 - β) * σ ^ 2

/-- `π_R(0) = π̄_R + βσ²/2` (p. 252). -/
noncomputable def piR0 (a b c φ σ β : ℝ) : ℝ :=
  piRbar a b c φ + β * σ ^ 2 / 2

/-- `π_R(1) = π̄_R + [(1+2φ)/(1+φ) + 1/((1+φ)(2+(1+φ)c)²)] · βσ²/4` (p. 252). -/
noncomputable def piR1 (a b c φ σ β : ℝ) : ℝ :=
  piRbar a b c φ
    + ((1 + 2 * φ) / (1 + φ) + 1 / ((1 + φ) * (2 + (1 + φ) * c) ^ 2)) * (β * σ ^ 2 / 4)

/-- `π_R(2) = π̄_R + (1+φ)²βσ²/[2(2+φ+(1+φ)c)²]` (p. 252). -/
noncomputable def piR2 (a b c φ σ β : ℝ) : ℝ :=
  piRbar a b c φ + (1 + φ) ^ 2 / (2 * (2 + φ + (1 + φ) * c) ^ 2) * β * σ ^ 2

end InfoSharing.Shared


