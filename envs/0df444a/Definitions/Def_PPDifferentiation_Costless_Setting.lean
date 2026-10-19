-- Prove2me | Definitions.Def_PPDifferentiation_Costless_Setting
-- name    : PPDifferentiation_Costless_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T11:25:31.939966+00:00
-- url     : https://prove2.me/theorems/5bf52c6f-49bc-44fe-aac0-9652b2c904a9
-- title:
--   §3, §4, App. A — Hotelling duopoly with quadratic misfit: misfit advantage, Bertrand profits under PP, uniform-leader/targeted-follower and uniform-price stages
-- statement:
--   This file sets up the three-stage competition model of Li, Wang and Nault between two firms $A$ and $B$ that choose positions on a Hotelling line, then decide whether to implement personalized pricing (PP), then set prices. PP is costless here, so the stage-2 decision is only a choice between two pricing technologies.
--
--   **Consumers and misfit.** A unit mass of consumers is uniformly distributed on $[0,1]$; each buys exactly one unit (the market is covered). A consumer at $x$ who buys from a firm located at $x_j\in\mathbb R$ incurs the misfit cost $t(x-x_j)^2$, where $t>0$. For firms $i$ and $j$ at positions $x_i$ and $x_j$, the **misfit advantage** of $i$ over $j$ at $x$ is
--   $$\operatorname{adv}_t(x_i,x_j;x)=t(x-x_j)^2-t(x-x_i)^2,$$
--   the amount by which the consumer at $x$ prefers $i$ to $j$ at equal prices.
--
--   **Both firms implement PP.** Each consumer is contested à la Bertrand: the firm with the positive advantage charges that advantage and wins, the other charges $0$. Firm $i$'s profit against $j$ is
--   $$\pi^{PP}_t(x_i,x_j)=\int_0^1\max\{0,\operatorname{adv}_t(x_i,x_j;x)\}\,dx .$$
--   Firm $A$ earns $\pi^{PP}_t(x_A,x_B)$ and firm $B$ earns $\pi^{PP}_t(x_B,x_A)$.
--
--   **Only one firm implements PP.** The uniform-price firm $i$ moves first with a price $p$; then the targeting firm $j$ sets a price for every consumer. A consumer indifferent between the two offers buys from the targeting firm, so the leader keeps exactly the consumers with $p<\operatorname{adv}_t(x_i,x_j;x)$. The leader's share and profit are
--   $$D^{L}_t(x_i,x_j;p)=\lambda\big(\{x\in[0,1]: p<\operatorname{adv}_t(x_i,x_j;x)\}\big),\qquad \pi^{L}_t(x_i,x_j;p)=p\,D^{L}_t(x_i,x_j;p),$$
--   with $\lambda$ the Lebesgue measure. A price $p$ is an **optimal leader price** if it maximizes $\pi^{L}_t(x_i,x_j;\cdot)$ over all $p\in\mathbb R$. The targeting follower charges each consumer the most that consumer accepts, $p-\operatorname{adv}_t(x_i,x_j;x)$, where this is positive, and earns
--   $$\pi^{F}_t(x_i,x_j;p)=\int_0^1\max\{0,\,p-\operatorname{adv}_t(x_i,x_j;x)\}\,dx .$$
--   In $\pi^L$ and $\pi^F$ the first position is always the leader's (the uniform-price firm).
--
--   **Neither firm implements PP.** The firms choose uniform prices $p_i,p_j$ simultaneously. Firm $i$'s share is the measure of consumers in $[0,1]$ whose full price (price plus misfit cost) is strictly lower at $i$, i.e. with $p_i-p_j<\operatorname{adv}_t(x_i,x_j;x)$, plus half the measure of the tied consumers; its profit is $p_i$ times that share. A pair $(p_A,p_B)$ is a **price equilibrium** if neither firm can raise its profit by changing its price to any real number.
--
--   **Dominance of PP.** At positions $(x_A,x_B)$, *PP is strictly dominant for both firms* means: optimal leader prices exist in both orientations and a price equilibrium exists; and for every such outcome, firm $A$ earns strictly more with PP than with uniform pricing against either choice of $B$ (PP/PP versus being the uniform leader; being the targeting follower versus the uniform-price equilibrium), and likewise for firm $B$.
--
--   **Position equilibrium.** $(x_A,x_B)$ is a position equilibrium of the game in which both firms implement PP if no firm can raise its PP/PP profit by moving to any other point of $\mathbb R$, including points beyond the rival.
--
--   These objects are the vocabulary of every statement of the mission.
--
--   **Formalization Note** The reservation value $v$ is omitted: the paper assumes it large enough for full coverage and it cancels from every profit. Prices range over $\mathbb R$ (the paper never restricts their sign). The tie rules are the paper's: under one-sided PP the indifferent consumer buys from the targeting firm (the "$\ge$" on p. 33); under uniform prices ties, which matter only for coincident firms, are split half-half. Stage-3 profits are defined from the primitives (integrals and measures of consumer sets), never by their closed forms. Shares are `(volume (S ∩ Set.Icc 0 1)).toReal`; the sets are measure-finite, so `toReal` loses nothing.
-- source:
--   Li, Wang, Nault, Is Personalized Pricing Profitable When Firms Can Differentiate?, working paper, SSRN abstract 3881900 (version of August 3, 2021), pp. 5–8 and 33–34, §3, §4 Stage 3, §5.1, proof of Lemma 1

import Mathlib

open MeasureTheory

namespace PPDifferentiation.Costless

/-- Misfit advantage of firm `i` (at position `xi`) over firm `j` (at position `xj`) for the consumer
at `x`, with misfit-cost rate `t`: `t (x - xj)^2 - t (x - xi)^2`. At equal prices the consumer prefers
firm `i` by exactly this amount. -/
def adv (t xi xj x : ℝ) : ℝ := t * (x - xj)^2 - t * (x - xi)^2

/-- Both firms implement PP: profit of firm `i` (at `xi`) against firm `j` (at `xj`). Per-consumer
Bertrand competition: for each consumer `x ∈ [0, 1]` the firm with the positive misfit advantage charges
that advantage and the other charges `0`, so firm `i` earns `max 0 (adv t xi xj x)` from consumer `x`.
Firm A's profit is `profPP t xA xB`, firm B's is `profPP t xB xA`. -/
noncomputable def profPP (t xi xj : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, max 0 (adv t xi xj x)

/-- Only firm `j` implements PP; firm `i` (at `xi`, the first position argument) is the uniform-price
leader charging `p`. Leader `i`'s market share: the Lebesgue measure of the consumers `x ∈ [0, 1]` with
`p < adv t xi xj x`, i.e. those the targeting follower `j` cannot win at a positive price (a consumer
indifferent between the two offers buys from the targeting firm). -/
noncomputable def leadShare (t xi xj p : ℝ) : ℝ :=
  (volume ({x : ℝ | p < adv t xi xj x} ∩ Set.Icc 0 1)).toReal

/-- Profit of the uniform-price leader `i` (at `xi`) charging `p` when only the follower `j` (at `xj`)
implements PP. -/
noncomputable def leadProf (t xi xj p : ℝ) : ℝ := p * leadShare t xi xj p

/-- `p` is an optimal uniform price of the leader `i` (at `xi`) against the targeting follower `j`
(at `xj`): it maximizes `leadProf t xi xj` over all real prices. -/
def IsLeaderOpt (t xi xj p : ℝ) : Prop :=
  ∀ q : ℝ, leadProf t xi xj q ≤ leadProf t xi xj p

/-- Profit of the targeting follower `j` (at `xj`, the SECOND position argument) against the uniform
leader `i` (at `xi`, the first position argument) charging `p`: the follower charges each consumer `x`
the most that consumer accepts, `p - adv t xi xj x`, where this is positive, and earns `0` elsewhere. -/
noncomputable def followProf (t xi xj p : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, max 0 (p - adv t xi xj x)

/-- Neither firm implements PP: market share of firm `i` (at `xi`, uniform price `pi`) against firm `j`
(at `xj`, uniform price `pj`). It is the measure of consumers in `[0, 1]` whose full price
(price plus misfit cost) is strictly lower at `i`, plus half the measure of the tied consumers. -/
noncomputable def uShare (t xi xj pi pj : ℝ) : ℝ :=
  (volume ({x : ℝ | pi - pj < adv t xi xj x} ∩ Set.Icc 0 1)).toReal +
  (volume ({x : ℝ | pi - pj = adv t xi xj x} ∩ Set.Icc 0 1)).toReal / 2

/-- Neither firm implements PP: profit of firm `i` (at `xi`, price `pi`) against firm `j`
(at `xj`, price `pj`). -/
noncomputable def uProf (t xi xj pi pj : ℝ) : ℝ := pi * uShare t xi xj pi pj

/-- `(pA, pB)` is a Nash equilibrium of the simultaneous uniform-price game between firm A (at `xA`)
and firm B (at `xB`): neither firm gains by changing its price to any real number. -/
def IsPriceNE (t xA xB pA pB : ℝ) : Prop :=
  (∀ q : ℝ, uProf t xA xB q pB ≤ uProf t xA xB pA pB) ∧
  (∀ q : ℝ, uProf t xB xA q pA ≤ uProf t xB xA pB pA)

/-- With costless PP, at positions `xA` (firm A) and `xB` (firm B), implementing PP strictly dominates
not implementing it for both firms in the stage-2 game. The stage-3 outcomes exist (an optimal leader
price in both orientations and a uniform-price equilibrium), and for every such outcome:
* firm A: against B's PP, PP/PP beats being the uniform leader; against B's U, being the targeting
  follower (B leads) beats the uniform-price equilibrium;
* firm B: the mirror comparisons. -/
def PPStrictlyDominant (t xA xB : ℝ) : Prop :=
  (∃ p : ℝ, IsLeaderOpt t xA xB p) ∧
  (∃ p : ℝ, IsLeaderOpt t xB xA p) ∧
  (∃ pA pB : ℝ, IsPriceNE t xA xB pA pB) ∧
  (∀ p : ℝ, IsLeaderOpt t xA xB p → leadProf t xA xB p < profPP t xA xB) ∧
  (∀ pA pB p : ℝ, IsPriceNE t xA xB pA pB → IsLeaderOpt t xB xA p →
    uProf t xA xB pA pB < followProf t xB xA p) ∧
  (∀ p : ℝ, IsLeaderOpt t xB xA p → leadProf t xB xA p < profPP t xB xA) ∧
  (∀ pA pB p : ℝ, IsPriceNE t xA xB pA pB → IsLeaderOpt t xA xB p →
    uProf t xB xA pB pA < followProf t xA xB p)

/-- `(xA, xB)` is a pure Nash equilibrium of the stage-1 position game when both firms implement PP
(payoffs `profPP`): neither firm gains by moving to any position on the real line. -/
def IsPosEqPP (t xA xB : ℝ) : Prop :=
  (∀ x : ℝ, profPP t x xB ≤ profPP t xA xB) ∧
  (∀ x : ℝ, profPP t x xA ≤ profPP t xB xA)

end PPDifferentiation.Costless


