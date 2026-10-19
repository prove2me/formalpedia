-- Prove2me | Definitions.Def_AdBlockers_Allow_Model
-- name    : AdBlockers_Allow_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:45.696364+00:00
-- url     : https://prove2.me/theorems/03051949-f0df-4f47-aa17-d5f72fab1abd
-- title:
--   Two platforms on a Hotelling line with Ban / Allow / Fee plans and an Ads / Fee benchmark: shares, revenues, stage-2 equilibrium, equilibrium (Sec. 3, pp. 14–18)
-- statement:
--   The platform-competition model of Despotakis, Ravi and Srinivasan, *The Beneficial Effects of Ad Blockers*, Section 3.
--
--   **Plans.** Each of two platforms chooses a plan: **Ban** (ban ad blockers, choose an ad intensity $a_i \ge 0$), **Allow** (allow ad blockers, choose an ad intensity $a_i \ge 0$) or **Fee** (no ads, choose a subscription fee $p_i \ge 0$). In the benchmark world without ad blockers a platform chooses **Ads** or **Fee**; Ads shows ads to every user and is identified with Ban, and Fee is the same plan as in the main model.
--
--   **Users.** Users lie on the Hotelling line $[0,1]$ with the platforms at the endpoints, and every user picks exactly one platform (full coverage). There are two segments: non-adblock users of mass $\lambda$ and ad sensitivity $\beta$, and adblock users of mass $\mu$ and ad sensitivity $\gamma$; the price sensitivity is $1$. At platform 1 with decision value $d_1$ the disutility of a non-adblock user is $\beta d_1$ under Ban and Allow and $d_1$ under Fee; that of an adblock user is $\gamma d_1$ under Ban, $0$ under Allow and $d_1$ under Fee (Figure 2); platform 2 is symmetric.
--
--   **Revenues.** Writing $s(\cdot,\cdot)$ for the clipped Hotelling share of the definition `Duopoly`, the revenue of platform 1 under plans $(s_1, s_2)$ and decision values $(d_1, d_2)$ is
--   $$
--   r_1 = \lambda\, s\big(D^N_{s_1}(d_1), D^N_{s_2}(d_2)\big)\, d_1 + \mu\, s\big(D^A_{s_1}(d_1), D^A_{s_2}(d_2)\big)\, \pi^A_{s_1}(d_1),
--   $$
--   where $D^N, D^A$ are the disutilities above and $\pi^A_{s}(d)$ is $d$ under Ban and Fee and $0$ under Allow (adblock users see no ads under Allow). The revenue $r_2$ of platform 2 is obtained by exchanging the roles of the two platforms.
--
--   **Equilibrium.** Platforms first choose plans, then decision values, then users choose. A **stage-2 equilibrium** for plans $(s_1, s_2)$ is a pure Nash equilibrium $(d_1, d_2)$, $d_i \ge 0$, of the game with payoffs $(r_1, r_2)$. The profile $(s_1, s_2; d_1, d_2)$ is an **equilibrium** if $(d_1, d_2)$ is a stage-2 equilibrium for $(s_1, s_2)$ and, for every plan $s'$, the subgame $(s', s_2)$ has a stage-2 equilibrium in which platform 1 earns at most $r_1(s_1, s_2; d_1, d_2)$, and likewise for platform 2.
--
--   **Formalization Note** All parameters are real numbers; theorems assume $\lambda, \mu, \beta, \gamma > 0$. The intrinsic value $m$ cancels under full coverage and does not appear. The equilibrium notion is subgame perfection restricted to the on-path subgame and the subgames reached by a unilateral stage-1 deviation; play after a joint deviation affects no incentive and is not required to exist. The benchmark game is the main game with both plans in $\{\text{Ban}, \text{Fee}\}$, via `BenchPlan.toPlan`.
-- source:
--   Despotakis, Ravi & Srinivasan, The Beneficial Effects of Ad Blockers, SSRN 3083119 (version of Nov. 28, 2017), pp. 14–18, Sections 3.1 (plans and revenues, p. 14), 3.2 (users, Figure 2, pp. 15–16), 3.3 (timeline, pp. 16–17), 3.4 (benchmark, footnote 35, p. 17); Appendix A.1, p. 42 (Ban ≡ Ads)

import Mathlib
import Definitions.Def_AdBlockers_Allow_Duopoly

namespace AdBlockers.Allow

/-- The three plans of a platform in the main model (Sec. 3.1, p. 14). -/
inductive Plan where
  | ban
  | allow
  | fee
  deriving DecidableEq

/-- The two plans of a platform in the benchmark world without ad blockers (Sec. 3.4, p. 17). -/
inductive BenchPlan where
  | ads
  | fee
  deriving DecidableEq

/-- The benchmark is the main model restricted to `{Ban, Fee}`: the Ads plan shows ads to every
user, exactly like Ban (footnote 35, p. 17; Appendix A.1, p. 42), and Fee is the same plan. -/
def BenchPlan.toPlan : BenchPlan → Plan
  | .ads => .ban
  | .fee => .fee

/-- Disutility of a non-adblock user (ad sensitivity `β`, price sensitivity 1) at a platform with
plan `s` and decision value `d` (ad intensity or fee), Figure 2, p. 16. -/
def disNon (β : ℝ) : Plan → ℝ → ℝ
  | .ban, d => β * d
  | .allow, d => β * d
  | .fee, d => d

/-- Disutility of an adblock user (ad sensitivity `γ`) at a platform with plan `s` and decision
value `d`, Figure 2, p. 16: under Allow the ad blocker removes every ad. -/
def disAdb (γ : ℝ) : Plan → ℝ → ℝ
  | .ban, d => γ * d
  | .allow, _ => 0
  | .fee, d => d

/-- Revenue a platform with plan `s` and decision value `d` earns per adblock user it serves
(p. 14): `d` under Ban and Fee, nothing under Allow. -/
def payAdb : Plan → ℝ → ℝ
  | .ban, d => d
  | .allow, _ => 0
  | .fee, d => d

/-- Revenue of platform 1 (p. 14) when the plans are `(s₁, s₂)` and the decision values
`(d₁, d₂)`: segment 1 (mass `lam`, non-adblock users) pays `d₁` per user served, segment 2 (mass
`μ`, adblock users) pays `payAdb s₁ d₁`; the shares are the full-coverage Hotelling shares. -/
noncomputable def rev₁ (lam μ β γ : ℝ) (s₁ s₂ : Plan) (d₁ d₂ : ℝ) : ℝ :=
  lam * hotellingShare (disNon β s₁ d₁) (disNon β s₂ d₂) * d₁
    + μ * hotellingShare (disAdb γ s₁ d₁) (disAdb γ s₂ d₂) * payAdb s₁ d₁

/-- Revenue of platform 2, by the symmetry of p. 16 (swap `1 - x ↔ x`, `a₁ ↔ a₂`, `p₁ ↔ p₂`). -/
noncomputable def rev₂ (lam μ β γ : ℝ) (s₁ s₂ : Plan) (d₁ d₂ : ℝ) : ℝ :=
  rev₁ lam μ β γ s₂ s₁ d₂ d₁

/-- Stage 2 (p. 17): given the plans `(s₁, s₂)`, the decision values `(d₁, d₂)` (each `≥ 0`) form
a pure Nash equilibrium of the revenue game. -/
def IsStage2NE (lam μ β γ : ℝ) (s₁ s₂ : Plan) (d₁ d₂ : ℝ) : Prop :=
  IsNashNonneg (rev₁ lam μ β γ s₁ s₂) (rev₂ lam μ β γ s₁ s₂) d₁ d₂

/-- Equilibrium of the two-stage game at plans `(s₁, s₂)` with decision values `(d₁, d₂)`: the
on-path subgame is in a stage-2 equilibrium, and after every unilateral stage-1 deviation of either
platform there is a stage-2 equilibrium of the deviation subgame that leaves the deviator no better
off. -/
def IsEquilibrium (lam μ β γ : ℝ) (s₁ s₂ : Plan) (d₁ d₂ : ℝ) : Prop :=
  IsStage2NE lam μ β γ s₁ s₂ d₁ d₂ ∧
    (∀ s' : Plan, ∃ e₁ e₂ : ℝ, IsStage2NE lam μ β γ s' s₂ e₁ e₂ ∧
      rev₁ lam μ β γ s' s₂ e₁ e₂ ≤ rev₁ lam μ β γ s₁ s₂ d₁ d₂) ∧
    (∀ s' : Plan, ∃ e₁ e₂ : ℝ, IsStage2NE lam μ β γ s₁ s' e₁ e₂ ∧
      rev₂ lam μ β γ s₁ s' e₁ e₂ ≤ rev₂ lam μ β γ s₁ s₂ d₁ d₂)

end AdBlockers.Allow


