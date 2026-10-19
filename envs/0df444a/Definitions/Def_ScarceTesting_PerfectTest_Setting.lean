-- Prove2me | Definitions.Def_ScarceTesting_PerfectTest_Setting
-- name    : ScarceTesting_PerfectTest_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T20:09:48.252064+00:00
-- url     : https://prove2.me/theorems/a917c0b2-a3af-43c9-a7d1-c353394d8e0e
-- title:
--   §2, pp. 7–12 — (φ,σ)-tests, thresholds (5), value of a test (2)–(4), request set, demand, uniform random availability, planner objective S (9), µ̄, δ, γ
-- statement:
--   The model of §2 of Drakopoulos and Randhawa. A unit mass of agents has private priors $\mu\in[0,1]$ of being infected, distributed with a density $f$ on $[0,1]$ (nonnegative, integrable, total mass $1$) and distribution function $F(x)=\int_0^x f(t)\,dt$. An agent who acts (seeks treatment) earns $\mathbb 1(I=1)-c$, where $c\in(0,1)$ is the normalized cost. A **$(\varphi,\sigma)$-test** has false positive rate $\varphi=P(T=1\mid I=0)$ and true positive rate $\sigma=P(T=1\mid I=1)$; the $(0,1)$-test is the **perfect test**.
--
--   1. The **critical values** of display (5):
--   $$t_L=\frac{c\varphi}{c\varphi+(1-c)\sigma},\qquad t_H=\frac{c(1-\varphi)}{c(1-\varphi)+(1-c)(1-\sigma)}.$$
--   2. The **value of a test** (displays (2)–(4)): $V_{test}(\mu)=U_{test}(\mu)-U_{no\text{-}test}(\mu)$ with $U_{no\text{-}test}(\mu)=(\mu-c)^+$ and
--   $$U_{test}(\mu)=\big(\mu\sigma-c(\mu\sigma+(1-\mu)\varphi)\big)^+ +\big(\mu(1-\sigma)-c(\mu(1-\sigma)+(1-\mu)(1-\varphi))\big)^+,$$
--   which is $\sum_{t\in\{1,0\}}P(T=t)\,\big(P(I=1\mid T=t)-c\big)^+$ written with joint probabilities.
--   3. The **request set**: agents with $\mu\in[0,1]$ and $V_{test}(\mu)>0$; the **demand** $D(\varphi,\sigma)$ is its $f$-mass.
--   4. The **availability** under uniformly random allocation of $\kappa$ kits: $\min\{1,\kappa/D\}$, equal to $1$ when $D\le\kappa$; and $A(a,b)=\min\{1,\kappa/(F(b)-F(a))\}$ as a function of two thresholds.
--   5. The **planner's objective** (display (9) with $\alpha=1$): the planner gains $1$ for each infected and loses $\beta$ for each uninfected agent who acts. An untested agent acts iff $\mu\ge c$, contributing $\mu-\beta(1-\mu)$; a requesting agent is tested with probability $A=\min\{1,\kappa/D(\varphi,\sigma)\}$ and then acts iff the result is positive, contributing $\mu\sigma-\beta(1-\mu)\varphi$, and otherwise behaves as untested. Then
--   $$S(\varphi,\sigma)=\int_0^1 \mathrm{payoff}_{\varphi,\sigma}(\mu)\,f(\mu)\,d\mu.$$
--   6. The constants $\bar\mu=\int_0^1\mu f(\mu)\,d\mu$, $\delta=\int_c^1(1-\mu)f(\mu)\,d\mu$ and $\gamma=\int_0^c\mu f(\mu)\,d\mu$ (p. 22).
--
--   These are the objects of Proposition 2 and of every step of its proof.
--
--   **Formalization Note** All quantities are real-valued. $U_{test}$ is written without conditional probabilities so that no $0/0$ arises when $P(T=t)=0$. The availability is an `if` (Lean's $\kappa/0=0$ would otherwise give availability $0$ at zero demand instead of the printed $\min\{1,\infty\}=1$). Requesting is "strictly positive value"; an untested agent with $\mu=c$ acts and a tested agent at indifference after a positive result acts — these tie conventions concern a null set of priors.
-- source:
--   Drakopoulos & Randhawa, Why Perfect Tests May Not Be Worth Waiting For: Information as a Commodity, SSRN 3565245 (version of January 13, 2021), §2.1–§2.3, displays (1)–(10), pp. 7–12; δ, γ from the proof of Proposition 2, p. 22

import Mathlib

namespace ScarceTesting.PerfectTest

open MeasureTheory Set

noncomputable section

/-- The lower critical value `t_L = cφ / (cφ + (1 − c)σ)` of display (5), p. 10. -/
def tL (c φ σ : ℝ) : ℝ := c * φ / (c * φ + (1 - c) * σ)

/-- The upper critical value `t_H = c(1 − φ) / (c(1 − φ) + (1 − c)(1 − σ))` of display (5), p. 10. -/
def tH (c φ σ : ℝ) : ℝ := c * (1 - φ) / (c * (1 - φ) + (1 - c) * (1 - σ))

/-- Expected utility of taking a `(φ,σ)`-test, display (3), for an agent with prior `μ` and cost
ratio `c` (with `d = 1`), written in joint-probability form:
`Σ_{t ∈ {1,0}} max{0, P(I = 1, T = t) − c·P(T = t)}`, where
`P(I = 1, T = 1) = μσ`, `P(T = 1) = μσ + (1 − μ)φ`, `P(I = 1, T = 0) = μ(1 − σ)`,
`P(T = 0) = μ(1 − σ) + (1 − μ)(1 − φ)`. -/
def Utest (c φ σ μ : ℝ) : ℝ :=
  max 0 (μ * σ - c * (μ * σ + (1 - μ) * φ)) +
    max 0 (μ * (1 - σ) - c * (μ * (1 - σ) + (1 - μ) * (1 - φ)))

/-- Expected utility without the test, display (4): `(μ − c)⁺`. -/
def UnoTest (c μ : ℝ) : ℝ := max 0 (μ - c)

/-- The value of a `(φ,σ)`-test to an agent with prior `μ`, display (2). -/
def Vtest (c φ σ μ : ℝ) : ℝ := Utest c φ σ μ - UnoTest c μ

/-- The cumulative distribution function of the priors, `F(x) = ∫_0^x f`. -/
def cdf (f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in (0:ℝ)..x, f t

/-- `f` is a probability density of the priors on `[0,1]` (§2.2, p. 8). -/
structure IsPriorDensity (f : ℝ → ℝ) : Prop where
  nonneg : ∀ μ ∈ Icc (0:ℝ) 1, 0 ≤ f μ
  integrable : IntervalIntegrable f volume 0 1
  total : ∫ μ in (0:ℝ)..1, f μ = 1

/-- The priors of the agents who request a `(φ,σ)`-test: those who obtain positive value from it. -/
def requestSet (c φ σ : ℝ) : Set ℝ := {μ | μ ∈ Icc (0:ℝ) 1 ∧ 0 < Vtest c φ σ μ}

/-- The demand `D(φ,σ)` for a `(φ,σ)`-test: the mass of requesting agents. -/
def demand (f : ℝ → ℝ) (c φ σ : ℝ) : ℝ := ∫ μ in requestSet c φ σ, f μ

/-- The availability `min{1, κ/D}` under uniformly random allocation of `κ` kits among a requesting
mass `D`; equal to `1` when `D ≤ κ` (in particular when `D = 0`, the printed `min{1, ∞}`). -/
def availability (κ D : ℝ) : ℝ := if D ≤ κ then 1 else κ / D

/-- The availability `A(t_L, t_H) = min{1, κ / (F(t_H) − F(t_L))}` (p. 11) as a function of the two
thresholds. -/
def availThr (f : ℝ → ℝ) (κ a b : ℝ) : ℝ := availability κ (cdf f b - cdf f a)

/-- Planner's payoff (benefit `1` per infected tagged agent, cost `β` per uninfected tagged agent)
from an untested agent with prior `μ`, who acts (and is tagged) iff `μ ≥ c`. -/
def untestedPayoff (c β μ : ℝ) : ℝ := if c ≤ μ then μ - β * (1 - μ) else 0

/-- Planner's expected payoff from an agent with prior `μ` when a `(φ,σ)`-test is offered: an
agent who requests (positive value) is tested with probability `A`, and then acts iff the result
is positive (tagged infected w.p. `μσ`, uninfected w.p. `(1 − μ)φ`); otherwise the agent behaves as
untested. -/
def agentPayoff (f : ℝ → ℝ) (c β κ φ σ μ : ℝ) : ℝ :=
  if 0 < Vtest c φ σ μ then
    availability κ (demand f c φ σ) * (μ * σ - β * (1 - μ) * φ) +
      (1 - availability κ (demand f c φ σ)) * untestedPayoff c β μ
  else untestedPayoff c β μ

/-- The planner's objective `S(φ,σ)`, display (9) with `α = 1`. -/
def S (f : ℝ → ℝ) (c β κ φ σ : ℝ) : ℝ := ∫ μ in (0:ℝ)..1, agentPayoff f c β κ φ σ μ * f μ

/-- The mean prior `μ̄ = ∫_0^1 μ f(μ) dμ`. -/
def meanPrior (f : ℝ → ℝ) : ℝ := ∫ μ in (0:ℝ)..1, μ * f μ

/-- `δ = ∫_c^1 (1 − μ) f(μ) dμ` (proof of Proposition 2, p. 22). -/
def deltaC (f : ℝ → ℝ) (c : ℝ) : ℝ := ∫ μ in c..1, (1 - μ) * f μ

/-- `γ = ∫_0^c μ f(μ) dμ` (proof of Proposition 2, p. 22). -/
def gammaC (f : ℝ → ℝ) (c : ℝ) : ℝ := ∫ μ in (0:ℝ)..c, μ * f μ

end

end ScarceTesting.PerfectTest


