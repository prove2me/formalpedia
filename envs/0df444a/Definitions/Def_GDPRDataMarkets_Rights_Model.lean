-- Prove2me | Definitions.Def_GDPRDataMarkets_Rights_Model
-- name    : GDPRDataMarkets_Rights_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T22:58:13.794411+00:00
-- url     : https://prove2.me/theorems/be740c5e-0ca9-41f2-8bfd-a249b9da6005
-- title:
--   §2–§3.1, pp. 9–15 — parameters, Assumption 1, the two-period monopoly with privacy rights and its equilibrium
-- statement:
--   This file sets up the monopoly model of Ke and Sudhir with **privacy rights** (the right to opt in to data collection separately from purchase, and the right to erase one's data).
--
--   **Parameters.** Consumers value personalization at $(1+\kappa)v$, where $v$ is the value of the basic good and $\kappa\in\{\kappa_L,\kappa_H\}$ with probability $1/2$ each. Write $\mu=(\kappa_H+\kappa_L)/2$ and $\sigma=(\kappa_H-\kappa_L)/2$. The discount factor is $\delta$ and $c$ is the expected data-breach cost per period during which the firm holds a consumer's data. The standing assumptions are $\kappa_H>\kappa_L>0$, $\delta\in(0,1]$ and $c\ge 0$, and **Assumption 1** is
--   $$\mu\ \ge\ \max\Big\{(3+\delta)\sigma,\ \tfrac12+(2+\delta)\sigma\Big\}.$$
--
--   **Consumers.** Valuations $v$ are uniform on $[0,1]$: the mass of a set $S\subseteq[0,1]$ of consumers is its Lebesgue measure. A consumer learns her $\kappa$ only after period 1; the firm never learns $\kappa$.
--
--   **Timing.** In period 1 the firm sets a price $p_1$ for the basic good and each consumer chooses one of: no purchase, purchase without opting in, or purchase and opt in (which costs $c$ and reveals $v$ to the firm). In period 2 the firm sets a basic price $p_2$ and, for each opted-in consumer $v$, a personalized price $r(v)$. A consumer who did not opt in buys the basic good iff $v\ge p_2$. An opted-in consumer of type $\kappa$ either keeps her data and buys the personalized good, with utility $(1+\kappa)v-r(v)-c$, or erases her data and takes $\max\{v-p_2,0\}$; she keeps on ties, and after erasing buys the basic good iff $v\ge p_2$.
--
--   **Strategy profile.** A profile $s$ consists of the first-period price $s.p_1$, a basic price $s.p_2(p_1)$ after every first-period price, a personalized price $s.r(v,q)$ for every valuation $v$ and basic price $q$, and a first-period action $s.\mathrm{choice}(p_1,v)$ of every consumer after every first-period price. The consumer's first-period payoffs are
--   $$U(\text{none})=\delta\max\{v-q,0\},\quad U(\text{buy})=v-p_1+\delta\max\{v-q,0\},\quad U(\text{opt in})=v-p_1-c+\delta\,\mathbb E_\kappa\max\{(1+\kappa)v-\rho-c,\ \max\{v-q,0\}\},$$
--   with $q=s.p_2(p_1)$ and $\rho=s.r(v,q)$. The firm's second-period profit at basic price $q$ is the integral, over the opted-in consumers, of the expected revenue $R(v,q,s.r(v,q))$ from each, plus $q$ times the mass of the other consumers with $v\ge q$. Its total profit at $p_1$ is $p_1$ times the mass of first-period buyers plus $\delta$ times the second-period profit at $s.p_2(p_1)$.
--
--   **Equilibrium.** $s$ is an equilibrium if (1) every personalized price $s.r(v,q)$ maximizes $R(v,q,\cdot)$; (2) after every $p_1$, the basic price $s.p_2(p_1)$ maximizes the second-period profit over all real $q$; (3) after every $p_1$, every consumer's action maximizes her first-period payoff; (4) $s.p_1$ maximizes the total profit over all real $p_1$.
--
--   This is the game whose equilibrium Proposition 1 describes. Every optimality condition is required at every history, not only on the equilibrium path.
--
--   **Formalization Note** `Params` has fields `kL`, `kH`, `d` (for $\delta$) and `c`; `Standing` and `Assumption1` are predicates that every theorem takes as hypotheses. The expectation over $\kappa$ is the average of the $\kappa_L$ and $\kappa_H$ values. Profits are Bochner integrals and Lebesgue measures (`toReal`) of subsets of $[0,1]$, built from the consumers' own choices; the paper's closed forms are theorems, not definitions. $c\ge 0$ is not printed as an assumption; it is the paper's "expected cost", and Proposition 1 A states $0\le c$.
-- source:
--   Ke, Sudhir, Privacy Rights and Data Security: GDPR and Personal Data Markets, SSRN 3643979 (pdfTeX build 2022-09-14), pp. 9–15, §2, Assumption 1 (p. 11) and §3.1

import Mathlib

namespace GDPRDataMarkets.Rights

open MeasureTheory

/-- The first-period action of a consumer (p. 9): no purchase, purchase without opting in to data
collection, or purchase and opt in. -/
inductive FirstChoice
  | none
  | buy
  | optIn
  deriving DecidableEq

noncomputable section

/-- The parameters of the model (pp. 9–11): the two personalization benefits `κ_L`, `κ_H`, the
discount factor `δ`, and the expected data-breach cost `c` per period of data held by the firm. -/
structure Params where
  /-- `κ_L` -/
  kL : ℝ
  /-- `κ_H` -/
  kH : ℝ
  /-- the discount factor `δ` -/
  d : ℝ
  /-- expected breach cost per period of data held -/
  c : ℝ

/-- `μ = (κ_H + κ_L)/2` (p. 11). -/
def Params.mu (P : Params) : ℝ := (P.kH + P.kL) / 2

/-- `σ = (κ_H − κ_L)/2` (p. 11). -/
def Params.sigma (P : Params) : ℝ := (P.kH - P.kL) / 2

/-- pp. 9–11: `κ_H > κ_L > 0`, `δ ∈ (0, 1]`, `c ≥ 0`. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.kL ∧ P.kL < P.kH ∧ 0 < P.d ∧ P.d ≤ 1 ∧ 0 ≤ P.c

/-- Assumption 1, p. 11: `μ ≥ max{(3 + δ)σ, 1/2 + (2 + δ)σ}`. -/
def Params.Assumption1 (P : Params) : Prop :=
  max ((3 + P.d) * P.sigma) (1 / 2 + (2 + P.d) * P.sigma) ≤ P.mu

/-- A strategy profile of the two-period monopoly game with privacy rights (§3.1).
* `p1` — the firm's first-period price;
* `p2 p₁` — the firm's second-period basic price after first-period price `p₁`;
* `r v q` — the personalized price offered to an opted-in consumer of valuation `v` when the basic
  price is `q` (the firm learns `v` from opted-in consumers but never `κ`);
* `choice p₁ v` — the first-period action of a consumer of valuation `v` at first-period price `p₁`. -/
structure Profile where
  p1 : ℝ
  p2 : ℝ → ℝ
  r : ℝ → ℝ → ℝ
  choice : ℝ → ℝ → FirstChoice

/-- An opted-in consumer of valuation `v` and type `κ`, facing basic price `q` and personalized price
`ρ`, keeps her data and buys the personalized good (utility `(1 + κ)v − ρ − c`) rather than erasing
her data (utility `max{v − q, 0}`). Ties go to keeping (p. 12). -/
def keeps (P : Params) (v κ q ρ : ℝ) : Prop :=
  max (v - q) 0 ≤ (1 + κ) * v - ρ - P.c

/-- Second-period utility of an opted-in consumer of type `κ`:
`max{(1 + κ)v − ρ − c, max{v − q, 0}}` (p. 12). -/
def u2opt (P : Params) (v κ q ρ : ℝ) : ℝ :=
  max ((1 + κ) * v - ρ - P.c) (max (v - q) 0)

/-- Second-period revenue from an opted-in consumer of type `κ`: `ρ` if she keeps her data and buys
the personalized good; otherwise she erases her data and buys the basic good iff `v ≥ q`. -/
def rev2opt (P : Params) (v κ q ρ : ℝ) : ℝ :=
  if max (v - q) 0 ≤ (1 + κ) * v - ρ - P.c then ρ else if q ≤ v then q else 0

/-- Expected second-period revenue from an opted-in consumer of valuation `v`: `κ ∈ {κ_L, κ_H}` with
probability `1/2` each, unknown to the firm (p. 11–12). -/
def R (P : Params) (v q ρ : ℝ) : ℝ :=
  (rev2opt P v P.kL q ρ + rev2opt P v P.kH q ρ) / 2

/-- Total discounted utility of a consumer of valuation `v` at first-period price `p₁` from each
first-period action, anticipating the basic price `q = p₂(p₁)` and her personalized price
`ρ = r(v, q)`. A consumer who has not opted in buys the basic good in period 2 iff `v ≥ q`; opting in
costs `c` in period 1, and her period-2 utility is `u2opt`, averaged over `κ` (pp. 12–14). -/
def U1 (P : Params) (s : Profile) (p1 v : ℝ) : FirstChoice → ℝ
  | .none => P.d * max (v - s.p2 p1) 0
  | .buy => v - p1 + P.d * max (v - s.p2 p1) 0
  | .optIn => v - p1 - P.c + P.d * ((u2opt P v P.kL (s.p2 p1) (s.r v (s.p2 p1))
                                      + u2opt P v P.kH (s.p2 p1) (s.r v (s.p2 p1))) / 2)

/-- Consumers in `[0, 1]` who purchase and opt in at first-period price `p₁`. -/
def optInSet (s : Profile) (p1 : ℝ) : Set ℝ :=
  {v | v ∈ Set.Icc (0 : ℝ) 1 ∧ s.choice p1 v = .optIn}

/-- Consumers in `[0, 1]` who purchase in period 1 (with or without opting in). -/
def buyerSet (s : Profile) (p1 : ℝ) : Set ℝ :=
  {v | v ∈ Set.Icc (0 : ℝ) 1 ∧ s.choice p1 v ≠ .none}

/-- The firm's second-period profit after first-period price `p₁` when it sets basic price `q` and
personalized prices `s.r · q`: expected revenue from the opted-in consumers plus `q` times the mass
of the other consumers who buy the basic good (`v ≥ q`). Consumers are uniform on `[0, 1]`. -/
def profit2 (P : Params) (s : Profile) (p1 q : ℝ) : ℝ :=
  (∫ v in optInSet s p1, R P v q (s.r v q))
    + q * (volume {v | v ∈ Set.Icc (0 : ℝ) 1 ∧ s.choice p1 v ≠ .optIn ∧ q ≤ v}).toReal

/-- The firm's total discounted profit at first-period price `p₁`, given the continuation play
prescribed by `s`. -/
def profit (P : Params) (s : Profile) (p1 : ℝ) : ℝ :=
  p1 * (volume (buyerSet s p1)).toReal + P.d * profit2 P s p1 (s.p2 p1)

/-- `s` is an equilibrium of the monopoly game with privacy rights:
1. at every basic price `q`, each personalized price `s.r v q` maximizes the expected revenue from
   the opted-in consumer `v` (p. 12–13);
2. after every first-period price `p₁`, the basic price `s.p2 p₁` maximizes the second-period profit
   (p. 14);
3. at every first-period price `p₁`, every consumer's first-period action is optimal given the
   firm's continuation (p. 14);
4. the first-period price `s.p1` maximizes the firm's total profit over all real prices (p. 15). -/
def IsEquilibrium (P : Params) (s : Profile) : Prop :=
  (∀ v ∈ Set.Icc (0 : ℝ) 1, ∀ q ρ : ℝ, R P v q ρ ≤ R P v q (s.r v q)) ∧
  (∀ p1 q : ℝ, profit2 P s p1 q ≤ profit2 P s p1 (s.p2 p1)) ∧
  (∀ p1 : ℝ, ∀ v ∈ Set.Icc (0 : ℝ) 1, ∀ a : FirstChoice, U1 P s p1 v a ≤ U1 P s p1 v (s.choice p1 v)) ∧
  (∀ p1 : ℝ, profit P s p1 ≤ profit P s s.p1)

end

end GDPRDataMarkets.Rights


