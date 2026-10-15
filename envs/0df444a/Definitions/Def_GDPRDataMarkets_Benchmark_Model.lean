-- Prove2me | Definitions.Def_GDPRDataMarkets_Benchmark_Model
-- name    : GDPRDataMarkets_Benchmark_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T22:58:26.735857+00:00
-- url     : https://prove2.me/theorems/c5f51fef-6dce-4f5c-b11e-d52286c56001
-- title:
--   §2, §3.2 and pp. 48–51 — parameters, Assumption 1, the two-period monopoly without privacy rights and its equilibrium
-- statement:
--   This file sets up the benchmark model of Ke and Sudhir without privacy rights: a monopolist sells over two periods to a unit mass of consumers, and every purchase reveals the buyer's valuation to the firm, which keeps the data for good.
--
--   **Parameters.** Personalization benefits $\kappa_L,\kappa_H$, a discount factor $\delta$ and an expected data-breach cost $c$ per period during which the firm holds a consumer's data. Write $\mu=(\kappa_H+\kappa_L)/2$ and $\sigma=(\kappa_H-\kappa_L)/2$. The standing assumptions are $\kappa_H>\kappa_L>0$, $\delta\in(0,1]$ and $c\ge 0$, and **Assumption 1** is
--   $$\mu\ \ge\ \max\Big\{(3+\delta)\sigma,\ \tfrac12+(2+\delta)\sigma\Big\}.$$
--
--   **Consumers.** Valuations $v$ of the basic good are uniform on $[0,1]$, so the mass of a set of consumers is its Lebesgue measure. A consumer values the personalized good at $(1+\kappa)v$, where $\kappa\in\{\kappa_L,\kappa_H\}$ with probability $1/2$ each. She learns $\kappa$ only at the start of period 2, and the firm never observes it.
--
--   **Strategies.** A profile consists of a first-period price $p_1$; a second-period basic price $p_2(p_1)$, offered to first-period non-buyers after each first-period price $p_1$; a personalized price $r(v)$, offered to each first-period buyer, whose valuation $v$ the firm learned when she bought; and the consumers' first-period purchase decision at each $p_1$.
--
--   **Payoffs.** A consumer who buys in period 1 pays $p_1$ and bears $c$. In period 2 she gets $\max\{(1+\kappa)v-r(v)-c,\,-c\}$: the outside option still costs $c$ because the data cannot be erased. Her expected discounted utility is
--   $$U^{\mathrm{buy}}(v)=v-p_1-c+\delta\,\mathbb E_\kappa\big[\max\{(1+\kappa)v-r(v)-c,\,-c\}\big].$$
--   A consumer who waits gets $U^{\mathrm{wait}}(v)=\delta\max\{v-p_2(p_1)-c,\,0\}$; if she buys the basic good in period 2 she also bears $c$. Indifferent consumers buy. The firm's expected second-period revenue from a past buyer at price $\rho$ is $R(v,\rho)=\frac{\rho}{2}\big[\mathbb 1(\rho\le(1+\kappa_L)v)+\mathbb 1(\rho\le(1+\kappa_H)v)\big]$. Its second-period profit at basic price $q$ is the integral of $R(v,r(v))$ over the first-period buyers, plus $q$ times the measure of the first-period non-buyers with $v-q-c\ge 0$. Its total profit at $p_1$ is $p_1$ times the measure of first-period buyers, plus $\delta$ times the second-period profit at $q=p_2(p_1)$.
--
--   **Equilibrium.** A profile is an equilibrium if four conditions hold:
--   1. $r(v)$ maximizes $R(v,\cdot)$ for every $v\in[0,1]$;
--   2. after every $p_1$, the price $p_2(p_1)$ maximizes second-period profit given the first-period buyers at $p_1$;
--   3. after every $p_1$, each consumer's first-period choice is optimal given $p_2(p_1)$ and $r$;
--   4. $p_1$ maximizes total profit over all real prices.
--
--   The file also names the closed-form constants of Proposition 2: $T_1=\frac{2-\delta+2\delta\sigma}{2-\delta+2\delta\mu+2\delta\sigma}$, $T_2=1+\frac{\delta}{1+\delta}\mu$, $P_1^B$ (eq. (7)), $p^B_{2M}$, $\overline v_1^B$, $\underline v_1^B$, $v_2^B$ and $P_2^B$.
--
--   **Formalization Note.** The standing conditions are bundled as `Params.Standing` and Assumption 1 as `Params.Assumption1`. $c\ge0$ is not printed as an assumption; it is the paper's "expected cost". The expectation over $\kappa$ is the average of the two types. The price $p_2$ depends on the history only through $p_1$: in equilibrium the set of first-period buyers is determined by $p_1$ up to a single indifferent valuation. Past buyers are offered only the personalized good, as in the paper. $P_1^B$ is eq. (7) with the stray $\kappa$ of the printed numerator $(2-\delta+2\delta\sigma\kappa)^2$ removed.
-- source:
--   Ke, Sudhir, Privacy Rights and Data Security: GDPR and Personal Data Markets, SSRN 3643979 (pdfTeX build 2022-09-14), pp. 9–12 (§2, Assumption 1), p. 16 (§3.2), pp. 48–51 (Appendix, proof of Proposition 2, eqs. (5)–(8))

import Mathlib

namespace GDPRDataMarkets.Benchmark

open MeasureTheory

/-- The parameters of the model (§2, pp. 9–11): the two personalization benefits `κ_L`, `κ_H`,
the discount factor `δ`, and the expected data-breach cost `c` per period of data held. -/
structure Params where
  kL : ℝ   -- κ_L
  kH : ℝ   -- κ_H
  d  : ℝ   -- the discount factor δ
  c  : ℝ   -- expected breach cost per period of data held

/-- `μ = (κ_H + κ_L)/2` (p. 11). -/
noncomputable def Params.mu (P : Params) : ℝ := (P.kH + P.kL) / 2

/-- `σ = (κ_H − κ_L)/2` (p. 11). -/
noncomputable def Params.sigma (P : Params) : ℝ := (P.kH - P.kL) / 2

/-- pp. 9–11: κ_H > κ_L > 0, δ ∈ (0, 1], c ≥ 0 -/
def Params.Standing (P : Params) : Prop := 0 < P.kL ∧ P.kL < P.kH ∧ 0 < P.d ∧ P.d ≤ 1 ∧ 0 ≤ P.c

/-- Assumption 1, p. 11 -/
def Params.Assumption1 (P : Params) : Prop :=
  max ((3 + P.d) * P.sigma) (1 / 2 + (2 + P.d) * P.sigma) ≤ P.mu

/-- A strategy profile of the monopoly game without privacy rights (§3.2, appendix pp. 48–49).
* `p1` — the firm's first-period price of the basic good;
* `p2 p₁` — the firm's second-period price of the basic good, offered to the consumers who did not
  buy in period 1, after the first-period price `p₁`;
* `r v` — the firm's second-period price of the personalized good offered to a first-period
  buyer, whose valuation `v` the firm learned when she bought;
* `buy p₁ v` — whether a consumer of valuation `v` buys in period 1 at first-period price `p₁`. -/
structure Profile where
  p1  : ℝ
  p2  : ℝ → ℝ
  r   : ℝ → ℝ
  buy : ℝ → ℝ → Bool

/-- Second-period utility of a first-period buyer of valuation `v` and type `κ` facing the
personalized price `ρ`: keep buying, `(1 + κ)v − ρ − c`, or take the outside option, which still
costs `c` because the data cannot be erased (p. 48). -/
noncomputable def u2B (P : Params) (v κ ρ : ℝ) : ℝ := max ((1 + κ) * v - ρ - P.c) (-P.c)

/-- The firm's second-period revenue from a past buyer of valuation `v` and type `κ` at the
personalized price `ρ`: she buys iff `ρ ≤ (1 + κ)v` (an indifferent consumer buys). -/
noncomputable def revB (v κ ρ : ℝ) : ℝ := if ρ ≤ (1 + κ) * v then ρ else 0

/-- Expected second-period revenue from a past buyer of valuation `v` at price `ρ`; the firm
does not observe `κ`, which is `κ_L` or `κ_H` with probability `1/2` each (p. 48). -/
noncomputable def RB (P : Params) (v ρ : ℝ) : ℝ := (revB v P.kL ρ + revB v P.kH ρ) / 2

/-- Expected discounted utility of a consumer of valuation `v` who buys in period 1 at price
`p₁`: she pays `p₁` and bears `c` in period 1, and in period 2 learns `κ` and chooses optimally
between the personalized good at `r v` and the outside option `−c`. -/
noncomputable def U1buy (P : Params) (σ : Profile) (p1 v : ℝ) : ℝ :=
  v - p1 - P.c + P.d * ((u2B P v P.kL (σ.r v) + u2B P v P.kH (σ.r v)) / 2)

/-- Expected discounted utility of a consumer of valuation `v` who does not buy in period 1:
in period 2 she buys the basic good at `p₂(p₁)`, bearing `c`, or takes the outside option `0`. -/
noncomputable def U1wait (P : Params) (σ : Profile) (p1 v : ℝ) : ℝ :=
  P.d * max (v - σ.p2 p1 - P.c) 0

/-- The set of first-period buyers at first-period price `p₁`; valuations are uniform on
`[0, 1]`. -/
def buyerSet (σ : Profile) (p1 : ℝ) : Set ℝ := {v | v ∈ Set.Icc (0 : ℝ) 1 ∧ σ.buy p1 v = true}

/-- The firm's second-period profit after first-period price `p₁` when it sets the basic price
`q`: personalized revenue from the past buyers plus `q` times the mass of first-period non-buyers
who buy the basic good, i.e. those with `v − q − c ≥ 0`. Masses are Lebesgue measure. -/
noncomputable def profit2 (P : Params) (σ : Profile) (p1 q : ℝ) : ℝ :=
  (∫ v in buyerSet σ p1, RB P v (σ.r v))
  + q * (volume {v | v ∈ Set.Icc (0 : ℝ) 1 ∧ σ.buy p1 v = false ∧ q + P.c ≤ v}).toReal

/-- The firm's total discounted profit at first-period price `p₁`, given the continuation that
the profile prescribes after `p₁`. -/
noncomputable def profit (P : Params) (σ : Profile) (p1 : ℝ) : ℝ :=
  p1 * (volume (buyerSet σ p1)).toReal + P.d * profit2 P σ p1 (σ.p2 p1)

/-- Subgame-perfect equilibrium of the monopoly game without privacy rights:
1. the personalized price `r v` is revenue-maximizing for every valuation `v ∈ [0, 1]`;
2. after every first-period price `p₁`, the basic price `p₂(p₁)` maximizes second-period profit
   given the first-period purchases at `p₁`;
3. after every first-period price `p₁`, every consumer's first-period choice is optimal given
   `p₂(p₁)` and `r`;
4. the first-period price `p1` maximizes total profit over all real prices. -/
def IsEquilibrium (P : Params) (σ : Profile) : Prop :=
  (∀ v ∈ Set.Icc (0 : ℝ) 1, ∀ ρ : ℝ, RB P v ρ ≤ RB P v (σ.r v)) ∧
  (∀ p1 q : ℝ, profit2 P σ p1 q ≤ profit2 P σ p1 (σ.p2 p1)) ∧
  (∀ p1 : ℝ, ∀ v ∈ Set.Icc (0 : ℝ) 1,
     (σ.buy p1 v = true → U1wait P σ p1 v ≤ U1buy P σ p1 v) ∧
     (σ.buy p1 v = false → U1buy P σ p1 v ≤ U1wait P σ p1 v)) ∧
  (∀ p1 : ℝ, profit P σ p1 ≤ profit P σ σ.p1)

/-- The threshold `(2 − δ + 2δσ)/(2 − δ + 2δμ + 2δσ)` between cases A and B of Proposition 2. -/
noncomputable def T1 (P : Params) : ℝ :=
  (2 - P.d + 2 * P.d * P.sigma) / (2 - P.d + 2 * P.d * P.mu + 2 * P.d * P.sigma)

/-- The threshold `1 + δ/(1 + δ) · μ` between cases B and C of Proposition 2. -/
noncomputable def T2 (P : Params) : ℝ := 1 + P.d / (1 + P.d) * P.mu

/-- `P₁^B`, eq. (7), p. 49, with the stray `κ` of the printed numerator removed. -/
noncomputable def P1B (P : Params) : ℝ :=
  ((2 - P.d + 2 * P.d * P.sigma) ^ 2
    - (4 + 4 * P.d - P.d ^ 2 + 2 * P.d ^ 2 * P.sigma + 2 * P.d * (2 + P.d) * P.mu) * P.c)
  / (2 * (4 - P.d + 2 * P.d * P.mu + 2 * P.d * P.sigma))

/-- `p^B_2M = [P₁^B + δ(1 − σ)c]/(2 − δ + 2δσ)` (Proposition 2 A(ii), p. 17). -/
noncomputable def p2B (P : Params) : ℝ :=
  (P1B P + P.d * (1 - P.sigma) * P.c) / (2 - P.d + 2 * P.d * P.sigma)

/-- `v̄₁^B = v^B_M(P₁^B) = (2P₁^B + (2 + δ)c)/(2 − δ + 2δσ)` (p. 50). -/
noncomputable def vbar1B (P : Params) : ℝ :=
  (2 * P1B P + (2 + P.d) * P.c) / (2 - P.d + 2 * P.d * P.sigma)

/-- `v̲₁^B = p^B_2M(P₁^B) + c` (p. 50). -/
noncomputable def vlow1B (P : Params) : ℝ := p2B P + P.c

/-- `v₂^B = min{(1 + δσ + (1 + δ)c)/(2 + δ + δμ + δσ), c}` (p. 51). -/
noncomputable def v2B (P : Params) : ℝ :=
  min ((1 + P.d * P.sigma + (1 + P.d) * P.c) / (2 + P.d + P.d * P.mu + P.d * P.sigma)) P.c

/-- `P₂^B = min{((1 + δσ)² − (1 + δ)(1 + δ + δμ)c)/(2 + δ + δμ + δσ), δ(σ − 1)c}` (p. 51). -/
noncomputable def P2B (P : Params) : ℝ :=
  min (((1 + P.d * P.sigma) ^ 2 - (1 + P.d) * (1 + P.d + P.d * P.mu) * P.c)
        / (2 + P.d + P.d * P.mu + P.d * P.sigma))
      (P.d * (P.sigma - 1) * P.c)

end GDPRDataMarkets.Benchmark


