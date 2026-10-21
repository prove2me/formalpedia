-- Prove2me | Definitions.Def_BOGOPromo_NoStockpile_Model
-- name    : BOGOPromo_NoStockpile_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T16:22:53.937457+00:00
-- url     : https://prove2.me/theorems/3916ee7f-edb9-4dcc-9870-ebeffd7a5e80
-- title:
--   §3, pp. 12–21 — BOGO, price-reduction and single-price regimes: consumer purchase options, retailer profit, manufacturer-leader equilibrium
-- statement:
--   This file sets up the two-period, two-echelon promotion model of Section 3 (no stockpiling) of Li, Khouja, Pan and Zhou.
--
--   **Consumers.** A unit mass of consumers has valuations $v$ uniformly distributed on $[0,1]$. In each period a consumer values the first unit at $v$, a second unit at $\theta v$ with $0<\theta\le 1$, and further units at $0$. A consumer who buys $i$ units in period 1 and $j$ units in period 2 takes the purchase option $(i,j)$.
--
--   1. Under a **BOGO** with first-unit price $p_b$, second-unit price $p_g$ in period 1 and regular price $p_b$ in period 2, the options and net utilities are
--   $$u_{0,0}=0,\quad u_{1,1}=2(v-p_b),\quad u_{2,0}=(1+\theta)v-p_b-p_g,\quad u_{2,1}=2(v-p_b)+\theta v-p_g.$$
--   2. Under a **price reduction (PR)** with discount price $p_d$ in period 1 and regular price $p_r$ in period 2,
--   $$u_{0,0}=0,\ u_{1,0}=v-p_d,\ u_{1,1}=2v-p_r-p_d,\ u_{2,0}=(1+\theta)v-2p_d,\ u_{2,1}=(2+\theta)v-p_r-2p_d.$$
--   3. Under **no promotion (NP)** at a single price $p$, a consumer buys one unit in each period iff $v\ge p$.
--
--   Each consumer chooses a utility-maximizing option; among tied options the one with more units is taken, in the order $(2,1),(2,0),(1,1),(1,0),(0,0)$.
--
--   **Retailer.** At wholesale price $w$ the retailer's expected profit is the integral over $v\in[0,1]$ of the margin of the chosen option (revenue minus $w$ per unit), and the expected demand $D$ is the integral of the number of units bought. In the BOGO game the retailer chooses a single price $p\ge 0$ or a BOGO with $0\le p_g\le p_b$; in the PR game a single price $p\ge 0$ or a PR with $0\le p_d\le p_r$; in the NP game a single price $p\ge 0$. A best response maximizes the retailer's profit over the feasible policies of its game.
--
--   **Equilibrium.** The manufacturer, with unit cost $c$, leads (Stackelberg). An equilibrium of a game is a wholesale price $w\in(0,1]$ together with a retailer strategy $r$ that assigns a best response $r(w')$ to every $w'\in(0,1]$, such that $w$ maximizes the manufacturer's profit $(w'-c)\,D(r(w'))$ over $w'\in(0,1]$ (eqs. (3), (5)).
--
--   **Thresholds.**
--   $$\bar\theta=\theta-(1-\theta)\sqrt{\tfrac{\theta}{1+\theta}},\qquad \tilde c(\theta)=\theta-(1-\theta)\sqrt{\tfrac{2\theta}{1+2\theta}},\qquad \bar c(\theta)=\frac{\theta(4\theta-1)}{1+2\theta}-2(1-\theta)\sqrt{\tfrac{\theta}{1+\theta}}.$$
--
--   These objects are shared by every statement of the mission: Tables 2 and 3 of the paper are theorems about them, not definitions.
--
--   **Formalization Note** The page writes $p_g<p_b$; the feasible set uses $p_g\le p_b$ (and $p_d\le p_r$) because at $\theta=1$ the paper's own optimum has $p_g=p_b$. The tie-break only affects a null set of consumers and reproduces the closed interval ends of Tables 1 and 4. Profits and demands are interval integrals of step functions of $v$, which are integrable. The single-price option belongs to the menu of the BOGO and PR games because Propositions 1 and 3 compare promotion with a single price. Wholesale prices range over $(0,1]$, as in the propositions.
-- source:
--   Li, Khouja, Pan & Zhou, Buy-One-Get-One Promotions in a Two-Echelon Supply Chain, SSRN working paper 3561162, pp. 6, 12–21 (PDF 6, 12–21), §3.1–§3.2, Tables 1, 4, eqs. (1)–(5), Propositions 2–4 (thresholds)

import Mathlib

namespace BOGOPromo.NoStockpile

/-! Li, Khouja, Pan & Zhou, *Buy-One-Get-One Promotions in a Two-Echelon Supply Chain*,
SSRN working paper 3561162, §3 (pp. 12–21). Consumers have valuation `v ~ U[0,1]` for the first
unit in a period and `θ v` for the second (`0 < θ ≤ 1`); the market size is `1`. -/

/-- Purchase options under BOGO-NSP (p. 13): `(i, j)` = `i` units in period 1, `j` in period 2. -/
inductive BOpt
  | o00 | o11 | o20 | o21

/-- Purchase options under PR-NSP (p. 19). -/
inductive POpt
  | o00 | o10 | o11 | o20 | o21

/-- Net utilities under BOGO-NSP (p. 13): first unit `pb`, second unit `pg` in period 1,
regular price `pb` in period 2. -/
def bUtil (θ pb pg v : ℝ) : BOpt → ℝ
  | .o00 => 0
  | .o11 => 2 * (v - pb)
  | .o20 => (1 + θ) * v - pb - pg
  | .o21 => 2 * (v - pb) + θ * v - pg

/-- Net utilities under PR-NSP (p. 19): discount price `pd` in period 1, regular price `pr`
in period 2. -/
def pUtil (θ pr pd v : ℝ) : POpt → ℝ
  | .o00 => 0
  | .o10 => v - pd
  | .o11 => 2 * v - pr - pd
  | .o20 => (1 + θ) * v - 2 * pd
  | .o21 => (2 + θ) * v - pr - 2 * pd

open Classical in
/-- The consumer's utility-maximizing BOGO option; ties go to the option listed first in the
order `(2,1), (2,0), (1,1), (0,0)` (more units first). -/
noncomputable def bChoice (θ pb pg v : ℝ) : BOpt :=
  if ∀ o, bUtil θ pb pg v o ≤ bUtil θ pb pg v .o21 then .o21
  else if ∀ o, bUtil θ pb pg v o ≤ bUtil θ pb pg v .o20 then .o20
  else if ∀ o, bUtil θ pb pg v o ≤ bUtil θ pb pg v .o11 then .o11
  else .o00

open Classical in
/-- The consumer's utility-maximizing PR option; ties go to the option listed first in the
order `(2,1), (2,0), (1,1), (1,0), (0,0)`. -/
noncomputable def pChoice (θ pr pd v : ℝ) : POpt :=
  if ∀ o, pUtil θ pr pd v o ≤ pUtil θ pr pd v .o21 then .o21
  else if ∀ o, pUtil θ pr pd v o ≤ pUtil θ pr pd v .o20 then .o20
  else if ∀ o, pUtil θ pr pd v o ≤ pUtil θ pr pd v .o11 then .o11
  else if ∀ o, pUtil θ pr pd v o ≤ pUtil θ pr pd v .o10 then .o10
  else .o00

/-- Retailer's margin from one consumer choosing a BOGO option, at wholesale price `w`
(integrands of eqs. (1), (2)). -/
def bMargin (pb pg w : ℝ) : BOpt → ℝ
  | .o00 => 0
  | .o11 => 2 * pb - 2 * w
  | .o20 => pb + pg - 2 * w
  | .o21 => 2 * pb + pg - 3 * w

/-- Units bought by one consumer choosing a BOGO option. -/
def bUnits : BOpt → ℝ
  | .o00 => 0
  | .o11 => 2
  | .o20 => 2
  | .o21 => 3

/-- Retailer's margin from one consumer choosing a PR option, at wholesale price `w`. -/
def pMargin (pr pd w : ℝ) : POpt → ℝ
  | .o00 => 0
  | .o10 => pd - w
  | .o11 => pr + pd - 2 * w
  | .o20 => 2 * pd - 2 * w
  | .o21 => pr + 2 * pd - 3 * w

/-- Units bought by one consumer choosing a PR option. -/
def pUnits : POpt → ℝ
  | .o00 => 0
  | .o10 => 1
  | .o11 => 2
  | .o20 => 2
  | .o21 => 3

/-- Retailer's expected profit under a BOGO `(pb, pg)` at wholesale price `w`, `v ~ U[0,1]`. -/
noncomputable def bogoProfit (θ w pb pg : ℝ) : ℝ :=
  ∫ v in (0:ℝ)..1, bMargin pb pg w (bChoice θ pb pg v)

/-- Expected units sold under a BOGO `(pb, pg)`. -/
noncomputable def bogoDemand (θ pb pg : ℝ) : ℝ :=
  ∫ v in (0:ℝ)..1, bUnits (bChoice θ pb pg v)

/-- Retailer's expected profit under a price reduction `(pr, pd)` at wholesale price `w`. -/
noncomputable def prProfit (θ w pr pd : ℝ) : ℝ :=
  ∫ v in (0:ℝ)..1, pMargin pr pd w (pChoice θ pr pd v)

/-- Expected units sold under a price reduction `(pr, pd)`. -/
noncomputable def prDemand (θ pr pd : ℝ) : ℝ :=
  ∫ v in (0:ℝ)..1, pUnits (pChoice θ pr pd v)

/-- No promotion: a single price `p` in both periods, at most one unit per period; a consumer
buys one unit in each period iff `v ≥ p`. Retailer's expected profit. -/
noncomputable def npProfit (w p : ℝ) : ℝ :=
  ∫ v in (0:ℝ)..1, if p ≤ v then 2 * (p - w) else 0

/-- Expected units sold under no promotion at price `p`. -/
noncomputable def npDemand (p : ℝ) : ℝ :=
  ∫ v in (0:ℝ)..1, if p ≤ v then (2:ℝ) else 0

/-- The retailer's menu in the BOGO game: a single price, or a BOGO. -/
inductive BPolicy
  | single (p : ℝ)
  | bogo (pb pg : ℝ)

/-- The retailer's menu in the PR game: a single price, or a price reduction. -/
inductive PPolicy
  | single (p : ℝ)
  | priceRed (pr pd : ℝ)

/-- Feasible BOGO-game policies: prices nonnegative, BOGO price at most the regular price. -/
def BPolicy.Feasible : BPolicy → Prop
  | .single p => 0 ≤ p
  | .bogo pb pg => 0 ≤ pg ∧ pg ≤ pb

/-- Feasible PR-game policies: prices nonnegative, discount price at most the regular price. -/
def PPolicy.Feasible : PPolicy → Prop
  | .single p => 0 ≤ p
  | .priceRed pr pd => 0 ≤ pd ∧ pd ≤ pr

noncomputable def BPolicy.profit (θ w : ℝ) : BPolicy → ℝ
  | .single p => npProfit w p
  | .bogo pb pg => bogoProfit θ w pb pg

noncomputable def BPolicy.demand (θ : ℝ) : BPolicy → ℝ
  | .single p => npDemand p
  | .bogo pb pg => bogoDemand θ pb pg

/-- Regular (period-2) price of a BOGO-game policy. -/
def BPolicy.regPrice : BPolicy → ℝ
  | .single p => p
  | .bogo pb _ => pb

/-- Promotional price of a BOGO-game policy (the single price if there is no promotion). -/
def BPolicy.promoPrice : BPolicy → ℝ
  | .single p => p
  | .bogo _ pg => pg

noncomputable def PPolicy.profit (θ w : ℝ) : PPolicy → ℝ
  | .single p => npProfit w p
  | .priceRed pr pd => prProfit θ w pr pd

noncomputable def PPolicy.demand (θ : ℝ) : PPolicy → ℝ
  | .single p => npDemand p
  | .priceRed pr pd => prDemand θ pr pd

/-- Regular (period-2) price of a PR-game policy. -/
def PPolicy.regPrice : PPolicy → ℝ
  | .single p => p
  | .priceRed pr _ => pr

/-- Promotional (period-1 discount) price of a PR-game policy. -/
def PPolicy.promoPrice : PPolicy → ℝ
  | .single p => p
  | .priceRed _ pd => pd

/-- Retailer best response in the BOGO game at wholesale price `w`. -/
def IsBestRespB (θ w : ℝ) (π : BPolicy) : Prop :=
  π.Feasible ∧ ∀ π' : BPolicy, π'.Feasible → π'.profit θ w ≤ π.profit θ w

/-- Retailer best response in the PR game at wholesale price `w`. -/
def IsBestRespP (θ w : ℝ) (π : PPolicy) : Prop :=
  π.Feasible ∧ ∀ π' : PPolicy, π'.Feasible → π'.profit θ w ≤ π.profit θ w

/-- Retailer best response in the no-promotion game at wholesale price `w`. -/
def IsBestRespN (w p : ℝ) : Prop :=
  0 ≤ p ∧ ∀ p' : ℝ, 0 ≤ p' → npProfit w p' ≤ npProfit w p

/-- Subgame-perfect equilibrium of the BOGO game, manufacturer leading (p. 6), with unit cost `c`:
the manufacturer's wholesale price `w ∈ (0,1]`, and a retailer strategy `r` that is a best response
at every wholesale price in `(0,1]`; `w` maximizes the manufacturer's profit `(w - c) D`, eq. (3). -/
def IsEqB (θ c w : ℝ) (r : ℝ → BPolicy) : Prop :=
  w ∈ Set.Ioc (0:ℝ) 1 ∧ (∀ w' ∈ Set.Ioc (0:ℝ) 1, IsBestRespB θ w' (r w')) ∧
    ∀ w' ∈ Set.Ioc (0:ℝ) 1, (w' - c) * (r w').demand θ ≤ (w - c) * (r w).demand θ

/-- Subgame-perfect equilibrium of the PR game, manufacturer leading; eq. (5). -/
def IsEqP (θ c w : ℝ) (r : ℝ → PPolicy) : Prop :=
  w ∈ Set.Ioc (0:ℝ) 1 ∧ (∀ w' ∈ Set.Ioc (0:ℝ) 1, IsBestRespP θ w' (r w')) ∧
    ∀ w' ∈ Set.Ioc (0:ℝ) 1, (w' - c) * (r w').demand θ ≤ (w - c) * (r w).demand θ

/-- Subgame-perfect equilibrium of the no-promotion game, manufacturer leading. -/
def IsEqN (c w : ℝ) (r : ℝ → ℝ) : Prop :=
  w ∈ Set.Ioc (0:ℝ) 1 ∧ (∀ w' ∈ Set.Ioc (0:ℝ) 1, IsBestRespN w' (r w')) ∧
    ∀ w' ∈ Set.Ioc (0:ℝ) 1, (w' - c) * npDemand (r w') ≤ (w - c) * npDemand (r w)

/-- `θ̄ = θ − (1 − θ)√(θ/(1+θ))`, Proposition 3, p. 20. -/
noncomputable def thetaBar (θ : ℝ) : ℝ := θ - (1 - θ) * Real.sqrt (θ / (1 + θ))

/-- `c̃(θ) = θ − (1 − θ)√(2θ/(1+2θ))`, Proposition 2, p. 16. -/
noncomputable def cTilde (θ : ℝ) : ℝ := θ - (1 - θ) * Real.sqrt (2 * θ / (1 + 2 * θ))

/-- `c̄(θ) = θ(4θ−1)/(1+2θ) − 2(1 − θ)√(θ/(1+θ))`, Proposition 4, p. 21. -/
noncomputable def cBar (θ : ℝ) : ℝ :=
  θ * (4 * θ - 1) / (1 + 2 * θ) - 2 * (1 - θ) * Real.sqrt (θ / (1 + θ))

end BOGOPromo.NoStockpile


