-- Prove2me | Definitions.Def_DigitalPrivacy_Strategy_Setting
-- name    : DigitalPrivacy_Strategy_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T02:29:01.045647+00:00
-- url     : https://prove2.me/theorems/5a9449fe-bed1-4e57-ae07-2e458b26a788
-- title:
--   §2–§4 — equilibrium activity ā* (3), CS (4), profit Π (2), feasible strategies, C_h, κ, C_l, ψ_L, ξ_i and the closed forms ξ*, C* (5)–(6)
-- statement:
--   This file sets up the model of Fainmesser, Galeotti and Momot's *Digital Privacy*. A digital business serves a unit mass of identical users and chooses a **data strategy** $(\xi, C)$: the fraction $\xi \in [0,1]$ of each user's activity it stores, and a data protection level $C \ge 0$ that costs $\psi C$. The parameters are the network effect $\beta$, the users' benefit $\rho$ from stored data, the unit protection cost $\psi$, and the share $P$ of revenue that is data-driven.
--
--   1. **Users.** A user choosing activity $a \ge 0$ when average activity is $\bar a$ and the mass of active adversaries is $\omega$ has utility (1)
--   $$U(a, \bar a) = a - \tfrac12 a^2 + \beta a \bar a + (\rho - \omega) a \xi .$$
--   2. **Subgame equilibrium.** A pair $(\bar a, \omega)$ is a (symmetric) equilibrium of the users–adversaries subgame for $(\xi, C)$ if $\bar a \ge 0$, $\bar a$ maximizes $a \mapsto U(a, \bar a)$ over $a \ge 0$, and $\omega = \xi \bar a / C$, the mass of adversaries whose access cost $\gamma C$ (with $\gamma$ uniform on $[0, M]$, $M \to \infty$) is at most their gain $\bar a \xi$.
--   3. **Equilibrium activity, adversaries and consumer surplus**, displays (3)–(4):
--   $$\bar a^*(\xi, C) = \frac{C(1+\rho\xi)}{C(1-\beta)+\xi^2}, \qquad \omega^*(\xi, C) = \frac{\xi \bar a^*(\xi, C)}{C}, \qquad \mathrm{CS}(\xi, C) = \tfrac12 \bar a^*(\xi, C)^2 ,$$
--   with $\bar a^*(0, C) = 1/(1-\beta)$ for every $C$.
--   4. **Profit** (2): $\Pi(\xi, C) = (1-P)\,\bar a^*(\xi, C) + P\,\xi \bar a^*(\xi, C) - \psi C$. A **feasible** strategy has $\xi \in [0,1]$ and $C \ge 0$; a **business optimum** is a feasible strategy maximizing $\Pi$ over all feasible strategies.
--   5. **Lemma 1 and Lemma 2 quantities**:
--   $$C_h(\xi) = \frac{1}{1-\beta}\Big(-\xi^2 + \xi\sqrt{\tfrac1\psi(1+\rho\xi)(1-P+P\xi)}\Big),\quad \kappa(C) = \frac{1-P-P\rho C(1-\beta)}{P+(1-P)\rho},\quad C_l = \frac{1}{1-\beta}\,\frac{2+\rho-P(1+\rho)}{P+\rho+P\rho},$$
--   and Lemma 2's interior data collection $-\kappa(C) + \sqrt{\kappa(C)^2 + C(1-\beta)}$.
--   6. **Thresholds and the interior root** (App. A.2): $\psi_L = (P+\rho+P\rho)^2/(4(1+\rho))$ and
--   $$\xi_i = \frac{1}{2P\rho}\Big(-(1-P)\rho - P + |P-(1-P)\rho|\sqrt{\tfrac{\psi}{\psi - P\rho}}\Big).$$
--   7. **The closed forms (5)–(6)**: $\xi^\star = 1$ if $\psi \le P\rho$, and $\xi^\star = \max\{0, \min\{1, \xi_i\}\}$ otherwise;
--   $$C^\star = \frac{\xi^\star}{1-\beta}\Big(-\xi^\star + \sqrt{\tfrac1\psi(1+\rho\xi^\star)(1-P(1-\xi^\star))}\Big).$$
--   8. **Parameter ranges.** `Basic`: $0 \le \beta < 1$, $0 \le \rho < 1$, $\psi > 0$, $0 \le P \le 1$. `Standing`: `Basic` together with $\rho > 0$ and $P > 0$.
--
--   These objects are shared by every statement of the mission: Proposition 1, Lemmas 1–2, the three-regime summary of App. A.2 and Theorem 1.
--
--   **Formalization Note**
--   1. Formula (3) is $0/0$ at $(\xi, C) = (0, 0)$. The paper uses the value $1/(1-\beta)$ there (App. A.2, $\pi_0 = (1-P)/(1-\beta)$; App. A.3, $\bar a_c = 1/(1-\beta)$), which is the users' best reply when nothing is stored; `abar` takes this value at $\xi = 0$ for every $C$, and agrees with (3) everywhere else. At $C = 0$, $\xi > 0$ it is $0$, as (3) gives.
--   2. In (5) the printed root $\sqrt{\psi/\max\{0, \psi - P\rho\}}$ is $+\infty$ when $\psi \le P\rho$, which, as App. A.2 (p. 31) says, guarantees $\xi^\star = 1$. The `xiStar` definition writes that branch out instead of relying on Lean's $x/0 = 0$. Formula (6) is kept verbatim in `CStar` (it equals $C_h(\xi^\star)$).
--   3. $\psi_H = (P+(1-P)\rho)^2/(4(1-P))$ is not defined as a number: the theorems use the condition $(P+(1-P)\rho)^2 \le 4(1-P)\psi$ for $\psi \ge \psi_H$, so that $\psi_H = +\infty$ at $P = 1$ needs no division by zero.
--   4. The paper allows $\psi \ge 0$; `Basic` requires $\psi > 0$, because $C_h$ and (6) contain $1/\psi$ and with $\psi = 0$ no profit maximizer exists. `Standing` adds $\rho > 0$, $P > 0$, because (5) divides by $2P\rho$.
--   5. The parameters are explicit real arguments; the profit is called `profit` in Lean.
-- source:
--   Fainmesser, Galeotti, Momot, Digital Privacy, author manuscript (This Draft: April 2022; SSRN 3459274), pp. 6–11, 28–31, (1)–(6), Lemmas 1–2, App. A.1–A.2

import Mathlib

namespace DigitalPrivacy.Strategy

/-! Fainmesser, Galeotti, Momot, *Digital Privacy*, author manuscript (This Draft: April 2022;
SSRN 3459274), §2–§4 and App. A.1–A.2. Parameters: network effect `β`, users' benefit from stored
data `ρ`, unit cost of protection `ψ`, data-driven revenue share `P`. A data strategy is a pair
`(ξ, C)`: the fraction `ξ` of activity stored and the protection level `C`. -/

/-- Equilibrium average user activity `ā*(ξ, C)`, display (3), p. 10:
`ā*(ξ, C) = C(1 + ρξ) / (C(1 − β) + ξ²)`. At `ξ = 0` the value is `1/(1 − β)` for every `C`,
the users' best reply when nothing is stored (App. A.2–A.3: `π₀ = (1−P)/(1−β)`,
`ā_c = 1/(1−β)`); this agrees with (3) for every `C > 0` and fixes the `0/0` of (3) at `(0, 0)`. -/
noncomputable def abar (β ρ ξ C : ℝ) : ℝ :=
  if ξ = 0 then 1 / (1 - β) else C * (1 + ρ * ξ) / (C * (1 - β) + ξ ^ 2)

/-- Equilibrium mass of active adversaries `ω*(ξ, C) = ξ ā*(ξ, C) / C`, display (3), p. 10. -/
noncomputable def omegaStar (β ρ ξ C : ℝ) : ℝ :=
  ξ * abar β ρ ξ C / C

/-- Consumer surplus `CS(ξ, C) = ā*(ξ, C)² / 2`, display (4), p. 10. -/
noncomputable def CS (β ρ ξ C : ℝ) : ℝ :=
  abar β ρ ξ C ^ 2 / 2

/-- The business's profit `Π(ξ, C) = (1 − P) ā* + P ξ ā* − ψ C`, display (2), p. 8. -/
noncomputable def profit (β ρ ψ P ξ C : ℝ) : ℝ :=
  (1 - P) * abar β ρ ξ C + P * (ξ * abar β ρ ξ C) - ψ * C

/-- Feasible data strategies: `ξ ∈ [0, 1]` and `C ≥ 0` (§2.3, p. 8). -/
def Feasible (ξ C : ℝ) : Prop :=
  ξ ∈ Set.Icc (0 : ℝ) 1 ∧ 0 ≤ C

/-- `(ξ, C)` is a business optimum: a feasible strategy maximizing `Π` over all feasible
strategies. -/
def IsBusinessOpt (β ρ ψ P ξ C : ℝ) : Prop :=
  Feasible ξ C ∧ ∀ ξ' C' : ℝ, Feasible ξ' C' → profit β ρ ψ P ξ' C' ≤ profit β ρ ψ P ξ C

/-- User utility (1), p. 7, of a user choosing activity `a` when average activity is `ā`, the
mass of active adversaries is `ω` and the stored fraction is `ξ`:
`U(a, ā) = a − a²/2 + β a ā + (ρ − ω) a ξ`. -/
noncomputable def userUtil (β ρ ξ ω ā a : ℝ) : ℝ :=
  a - a ^ 2 / 2 + β * a * ā + (ρ - ω) * a * ξ

/-- Symmetric equilibrium `(ā, ω)` of the users–adversaries subgame for a fixed data strategy
`(ξ, C)` (§2.1–§2.2 and App. A.1): the common activity `ā ≥ 0` is a best reply over `a ≥ 0` of
every (homogeneous) user to average activity `ā` and adversary mass `ω`, and `ω = ξ ā / C` is the
mass of adversaries with `γ C ≤ ā ξ` (`γ` uniform on `[0, M]`, `M → ∞`). -/
def IsSubgameEq (β ρ ξ C ā ω : ℝ) : Prop :=
  0 ≤ ā ∧ (∀ a : ℝ, 0 ≤ a → userUtil β ρ ξ ω ā a ≤ userUtil β ρ ξ ω ā ā) ∧ ω = ξ * ā / C

/-- `C_h(ξ) = (1/(1−β)) (−ξ² + ξ √((1/ψ)(1 + ρξ)(1 − P + Pξ)))`, Lemma 1, p. 29. -/
noncomputable def Ch (β ρ ψ P ξ : ℝ) : ℝ :=
  (1 / (1 - β)) * (-ξ ^ 2 + ξ * √((1 / ψ) * (1 + ρ * ξ) * (1 - P + P * ξ)))

/-- `κ(C) = (1 − P − PρC(1−β)) / (P + (1−P)ρ)`, Lemma 2, p. 29. -/
noncomputable def kappa (β ρ P C : ℝ) : ℝ :=
  (1 - P - P * ρ * C * (1 - β)) / (P + (1 - P) * ρ)

/-- `C_l = (1/(1−β)) (2 + ρ − P(1+ρ)) / (P + ρ + Pρ)`, Lemma 2, p. 29. -/
noncomputable def Cl (β ρ P : ℝ) : ℝ :=
  (1 / (1 - β)) * (2 + ρ - P * (1 + ρ)) / (P + ρ + P * ρ)

/-- Lemma 2's interior data collection `−κ(C) + √(κ(C)² + C(1−β))`, p. 29. -/
noncomputable def xiBR (β ρ P C : ℝ) : ℝ :=
  -kappa β ρ P C + √(kappa β ρ P C ^ 2 + C * (1 - β))

/-- The threshold `ψ_L = (P + ρ + Pρ)² / (4(1+ρ))`, App. A.2, p. 30. (The other threshold
`ψ_H = (P + (1−P)ρ)² / (4(1−P))` is used only through the condition
`(P + (1−P)ρ)² ≤ 4(1−P)ψ`, i.e. `ψ ≥ ψ_H`, with `ψ_H = +∞` at `P = 1`.) -/
noncomputable def psiL (ρ P : ℝ) : ℝ :=
  (P + ρ + P * ρ) ^ 2 / (4 * (1 + ρ))

/-- The interior root `ξ_i = (1/(2Pρ)) (−(1−P)ρ − P + |P − (1−P)ρ| √(ψ/(ψ − Pρ)))`,
App. A.2, p. 30; meaningful for `ψ > Pρ`. -/
noncomputable def xiI (ρ ψ P : ℝ) : ℝ :=
  (1 / (2 * P * ρ)) * (-(1 - P) * ρ - P + |P - (1 - P) * ρ| * √(ψ / (ψ - P * ρ)))

/-- `ξ*` of display (5), p. 11. For `ψ ≤ Pρ` the printed root `√(ψ / max{0, ψ − Pρ})` is `+∞`,
which (App. A.2, p. 31) "guarantees that ξ* = 1 is chosen"; that branch is written out. Otherwise
`ξ* = max{0, min{1, ξ_i}}`. -/
noncomputable def xiStar (ρ ψ P : ℝ) : ℝ :=
  if ψ ≤ P * ρ then 1 else max 0 (min 1 (xiI ρ ψ P))

/-- `C* = (ξ*/(1−β)) (−ξ* + √((1/ψ)(1 + ρξ*)(1 − P(1 − ξ*))))`, display (6), p. 11. -/
noncomputable def CStar (β ρ ψ P : ℝ) : ℝ :=
  xiStar ρ ψ P / (1 - β) *
    (-xiStar ρ ψ P + √((1 / ψ) * (1 + ρ * xiStar ρ ψ P) * (1 - P * (1 - xiStar ρ ψ P))))

/-- The page's parameter ranges with `ψ > 0` (disclosed addition): `0 ≤ β < 1` (p. 6),
`0 ≤ ρ < 1` (p. 6), `0 < ψ` (p. 8 has `ψ ≥ 0`), `0 ≤ P ≤ 1` (p. 8). -/
def Basic (β ρ ψ P : ℝ) : Prop :=
  0 ≤ β ∧ β < 1 ∧ 0 ≤ ρ ∧ ρ < 1 ∧ 0 < ψ ∧ 0 ≤ P ∧ P ≤ 1

/-- `Basic` together with `0 < ρ` and `0 < P` (disclosed additions: (5) divides by `2Pρ`). -/
def Standing (β ρ ψ P : ℝ) : Prop :=
  Basic β ρ ψ P ∧ 0 < ρ ∧ 0 < P

end DigitalPrivacy.Strategy


