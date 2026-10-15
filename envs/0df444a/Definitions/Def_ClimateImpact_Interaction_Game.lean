-- Prove2me | Definitions.Def_ClimateImpact_Interaction_Game
-- name    : ClimateImpact_Interaction_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T08:59:16.096202+00:00
-- url     : https://prove2.me/theorems/3d6d9c82-6053-4f26-8244-7db20be3c869
-- title:
--   Proposition 4, pp. 29–30 — interaction externality κ₀ − (κ/2)[(ψ^i)² + εψ^iψ̄], stage payoff F_i, stage Nash equilibrium, schedules (13) and (15)
-- statement:
--   The stage game with an interaction effect of Proposition 4.
--
--   For an emission profile $x\in\mathbb R^n$ let $\bar x=\frac1n\sum_{j=1}^n x^j$ be the **average emission**. For an **elasticity parameter** $\varepsilon\ge0$ the **externality with interaction effect** of company $i$ is
--   $$\theta^i(x)=\kappa_0-\frac{\kappa}{2}\big[(x^i)^2+\varepsilon\,x^i\bar x\big],$$
--   where the average $\bar x$ is that of the same profile $x$, so it moves when company $i$ changes $x^i$.
--
--   At a date $t$, company $i$'s **stage payoff** is
--   $$F_i(x)=\beta^c_t\Big(\kappa^c_{0,t}-\frac{\kappa^c_t}{2}\big[(x^i)^2+\varepsilon x^i\bar x\big]\Big)+\alpha\beta_t\Big(\kappa_{0,t}-\frac{\kappa_t}{2}\big[(x^i)^2+\varepsilon x^i\bar x\big]\Big)+c^i_t x^i .$$
--   A profile $x$ is a **stage Nash equilibrium** if for every company $i$ and every real $z$, replacing $x^i$ by $z$ (others fixed) does not raise $F_i$; the **nonnegative** variant requires $x\ge0$ and considers only deviations $z\ge0$.
--
--   Finally $\psi^{*,i}_t=c^i_t/(\beta^c_t\kappa^c_t+\alpha\beta_t\kappa_t)$ is the schedule (13) without interaction effect, $\bar\psi^*_t$ its average, and
--   $$\psi^{*,\varepsilon,i}_t=\psi^{*,i}_t-\frac{\varepsilon}{2n+\varepsilon}\Big(\psi^{*,i}_t+\frac{2n^2}{2n+(n+1)\varepsilon}\bar\psi^*_t\Big)$$
--   is the schedule (15) of Proposition 4(i).
--
--   **Formalization Note** The functions $\kappa,\kappa^c,\kappa_0,\kappa^c_0$ are maps $\mathbb R\to\mathbb R$ of time and the costs $c$ are indexed by company and time. The average divides by $n$; statements that use it assume $n>0$.
-- source:
--   SSRN 3562534 (25 Jun 2021), Proposition 4, pp. 29–30, (15); F_i, §6.3, p. 64; (13), p. 20

import Mathlib
import Definitions.Def_ClimateImpact_Interaction_TimeFactors

namespace ClimateImpact.Interaction

/-- The average emission `ψ̄ = (1/n) ∑_j ψ^j` of a profile (Proposition 4, p. 30). -/
noncomputable def avg {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  (∑ j, x j) / n

/-- The externality with interaction effect of Proposition 4 (p. 29):
`θ^i(ψ) = κ₀ - (κ/2) [(ψ^i)² + ε ψ^i ψ̄]`, where the average `ψ̄` is that of the same profile `ψ`. -/
noncomputable def interExt {n : ℕ} (κ₀ κ ε : ℝ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  κ₀ - κ / 2 * (x i ^ 2 + ε * x i * avg x)

/-- Company `i`'s date-`t` payoff `F_i` (§6.3, p. 64; (12), p. 19) with the externalities of
Proposition 4: `β^c_t θ^{c,i}_t(x) + α β_t θ^i_t(x) + c^i_t x^i`, where `θ^i_t` uses
`κ_{0,t}, κ_t` and `θ^{c,i}_t` uses `κ^c_{0,t}, κ^c_t`. -/
noncomputable def stagePayoff {n : ℕ} (ρ T α : ℝ) (κ κc κ₀ κc₀ : ℝ → ℝ) (c : Fin n → ℝ → ℝ)
    (ε t : ℝ) (i : Fin n) (x : Fin n → ℝ) : ℝ :=
  betaC ρ T t * interExt (κc₀ t) (κc t) ε x i + α * beta ρ T t * interExt (κ₀ t) (κ t) ε x i
    + c i t * x i

/-- `x ∈ ℝⁿ` is a Nash equilibrium of the date-`t` stage game: no company `i` gains by changing
its own emission `x^i` to any real `z`, the others' emissions held fixed. -/
def IsStageNash {n : ℕ} (ρ T α : ℝ) (κ κc κ₀ κc₀ : ℝ → ℝ) (c : Fin n → ℝ → ℝ) (ε t : ℝ)
    (x : Fin n → ℝ) : Prop :=
  ∀ (i : Fin n) (z : ℝ),
    stagePayoff ρ T α κ κc κ₀ κc₀ c ε t i (Function.update x i z)
      ≤ stagePayoff ρ T α κ κc κ₀ κc₀ c ε t i x

/-- `x ∈ ℝ₊ⁿ` is a Nash equilibrium of the date-`t` stage game played on nonnegative emissions
(footnote 7, p. 11). -/
def IsStageNashNonneg {n : ℕ} (ρ T α : ℝ) (κ κc κ₀ κc₀ : ℝ → ℝ) (c : Fin n → ℝ → ℝ) (ε t : ℝ)
    (x : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ ∀ (i : Fin n) (z : ℝ), 0 ≤ z →
    stagePayoff ρ T α κ κc κ₀ κc₀ c ε t i (Function.update x i z)
      ≤ stagePayoff ρ T α κ κc κ₀ κc₀ c ε t i x

/-- The schedule without interaction effect, `ψ^{*,i}_t = c^i_t / (β^c_t κ^c_t + α β_t κ_t)`
((13), Corollary 3, p. 20), as Proposition 4 recalls it. -/
noncomputable def noInt {n : ℕ} (ρ T α : ℝ) (κ κc : ℝ → ℝ) (c : Fin n → ℝ → ℝ) (t : ℝ)
    (i : Fin n) : ℝ :=
  noInteractionRate ρ T α (κ t) (κc t) (c i t) t

/-- The schedule (15) of Proposition 4(i) (p. 30):
`ψ^{*,ε,i}_t = ψ^{*,i}_t - ε/(2n+ε) (ψ^{*,i}_t + 2n²/(2n+(n+1)ε) ψ̄^*_t)`. -/
noncomputable def interactionRate {n : ℕ} (ρ T α : ℝ) (κ κc : ℝ → ℝ) (c : Fin n → ℝ → ℝ)
    (ε t : ℝ) (i : Fin n) : ℝ :=
  noInt ρ T α κ κc c t i
    - ε / (2 * n + ε)
      * (noInt ρ T α κ κc c t i
        + 2 * n ^ 2 / (2 * n + (n + 1) * ε) * avg (noInt ρ T α κ κc c t))

end ClimateImpact.Interaction


