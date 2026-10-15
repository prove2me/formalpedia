-- Prove2me | Definitions.Def_AdDataSharing_Topics_Model
-- name    : AdDataSharing_Topics_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:55.434992+00:00
-- url     : https://prove2.me/theorems/2e764e30-2fc9-470b-b26d-0c0592f9d1bd
-- title:
--   §3, pp. 16–17 and 29–30 — the Topics bidding game: parameters, payoffs, equilibria, ADX1 revenue, thresholds $w_1$, $w_2$, $\tilde\tau$
-- statement:
--   **The Topics model** (Johnson, Jungbauer and Preuss, §3). Two advertisers $A_1, A_2$ each bid on one of two ad exchanges. On $ADX_1$ the Topics system identifies the $1+\eta_2$ consumers interested in the product category, but it is imprecise: reaching a mass one of them takes $\tau>1$ ad impressions. On $ADX_2$ an advertiser retargets only a fraction $\sigma<1$ of the $1-\alpha$ consumers who recently visited its own website. An ad impression costs $w$; a consumer reached by one advertiser only is worth the monopoly profit $M$, and one reached by both is worth the competition profit $C$.
--
--   The parameters satisfy the standing assumptions
--   $$0<\alpha<\tfrac12,\quad 0<w<C<M<2C,\quad 0<\varphi<1,\quad \eta_2>0,\quad \tau>1,\quad 0\le\sigma<1 .$$
--
--   The profit $\pi(x,y)$ of an advertiser bidding on exchange $x$ when its rival bids on $y$ is
--
--   1. $\pi(ADX_1,ADX_1)=(1+\eta_2)(C-\tau w)$;
--   2. $\pi(ADX_2,ADX_2)=\sigma[\alpha M+(1-2\alpha)C-(1-\alpha)w]$;
--   3. $\pi(ADX_1,ADX_2)=(1+\eta_2)M-\sigma(1-\alpha)(M-C)-(1+\eta_2)\tau w$;
--   4. $\pi(ADX_2,ADX_1)=\sigma(1-\alpha)(C-w)$.
--
--   A profile $(x,y)$ ($A_1$ on $x$, $A_2$ on $y$) is an **equilibrium** when it is a pure-strategy Nash equilibrium of this symmetric two-player game: $\pi(x',y)\le\pi(x,y)$ and $\pi(y',x)\le\pi(y,x)$ for all exchanges $x',y'$. **ADX1's revenue** at $(x,y)$ is $\varphi w$ times the number of impressions sold on $ADX_1$, namely $\tau(1+\eta_2)$ for each advertiser bidding there.
--
--   Finally the model names the thresholds of the proof of Proposition 5,
--   $$w_1=\frac{(1+\eta_2)-\sigma(1-\alpha)}{\tau(1+\eta_2)-\sigma(1-\alpha)}\,C,\qquad w_2=\frac{[(1+\eta_2)-\sigma]M+\alpha\sigma C}{\tau(1+\eta_2)-\sigma(1-\alpha)},$$
--   and the accuracy threshold
--   $$\tilde\tau=\frac{(1+\eta_2)-\sigma(1-\alpha)}{w(1+\eta_2)}\,C+\frac{\sigma(1-\alpha)}{1+\eta_2}.$$
--
--   These objects are shared by every statement of the mission: Proposition 5 characterizes the equilibria through $w_1$, $w_2$ and $\tilde\tau$, and Proposition 7 and Corollary 2 compare ADX1's revenue across values of $\tau$ and $\sigma$.
--
--   **Formalization Note** The equilibrium notion is the platform's general two-player pure Nash equilibrium `CompetingChains.Cournot.IsPureNash`, applied with $u_1(x,y)=\pi(x,y)$ and $u_2(x,y)=\pi(y,x)$. The hypothesis $C>w$ is not stated in §3 but is used throughout the paper (p. 21: "it is profitable to target all customers"); $\sigma\ge 0$ is the reading of "a fraction $\sigma<1$". There is no contracting stage and no equilibrium selection in §3 (footnote 22). The threshold $\tilde\tau$ is the **corrected** one: the printed display (6) on p. 17 omits the factor $1/(1+\eta_2)$ on its first term. Outside the standing assumptions the divisions in $w_1, w_2, \tilde\tau$ may divide by zero (Lean returns $0$); every theorem assumes the standing assumptions, under which all denominators are positive.
-- source:
--   Johnson, Jungbauer, Preuss, Online Advertising, Data Sharing, and Consumer Control, SSRN 3898798 (Nov. 2, 2022), §3, pp. 16–17 (model and the four payoffs), Appendix pp. 29–30 (proof of Proposition 5: w1, w2), p. 30 (proof of Proposition 7: ADX1 revenue); threshold (6), p. 17, corrected

import Mathlib
import Definitions.Def_CompetingChains_Cournot_TwoPlayerGame
import Definitions.Def_AdDataSharing_Base_Model

namespace AdDataSharing.Topics

/-- Parameters of the Topics model (§1, pp. 4–6, and §3, pp. 16–17): `α` the mass of exclusive
    visitors of each website, `M` the monopoly profit, `C` the competition profit, `w` the price of an
    ad impression, `φ` the exchange's fee share, `η₂` the look-alike audience (so `1 + η₂` consumers are
    interested in the category), `τ` the impressions needed on ADX1 to reach a mass one of consumers,
    and `σ` the fraction of an advertiser's `1 − α` website visitors reachable on ADX2. -/
structure Params where
  α : ℝ
  M : ℝ
  C : ℝ
  w : ℝ
  φ : ℝ
  η₂ : ℝ
  τ : ℝ
  σ : ℝ

/-- Standing assumptions: §1 (pp. 4–6) α ∈ (0, 1/2), w > 0, C < M < 2C, φ ∈ (0, 1), η₂ > 0, together
    with C > w (used throughout the paper, cf. p. 21 and footnote 3), and §3 (pp. 16–17) τ > 1 and σ a
    fraction below one, 0 ≤ σ < 1. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.α ∧ P.α < 1 / 2 ∧ 0 < P.w ∧ P.w < P.C ∧ P.C < P.M ∧ P.M < 2 * P.C ∧
  0 < P.φ ∧ P.φ < 1 ∧ 0 < P.η₂ ∧ 1 < P.τ ∧ 0 ≤ P.σ ∧ P.σ < 1

/-- Profit of an advertiser bidding on exchange `x` when its rival bids on exchange `y` (the four
    displays of p. 17). -/
def payoff (P : Params) (x y : AdDataSharing.Base.Exchange) : ℝ :=
  match x, y with
  | .adx1, .adx1 => (1 + P.η₂) * (P.C - P.τ * P.w)
  | .adx2, .adx2 => P.σ * (P.α * P.M + (1 - 2 * P.α) * P.C - (1 - P.α) * P.w)
  | .adx1, .adx2 => (1 + P.η₂) * P.M - P.σ * (1 - P.α) * (P.M - P.C) - (1 + P.η₂) * P.τ * P.w
  | .adx2, .adx1 => P.σ * (1 - P.α) * (P.C - P.w)

/-- Pure Nash equilibrium of the symmetric 2 × 2 bidding game: advertiser A1 bids on `x`, advertiser
    A2 bids on `y`, and each one's payoff is `payoff` with its own exchange first. -/
def IsNE (P : Params) (x y : AdDataSharing.Base.Exchange) : Prop :=
  CompetingChains.Cournot.IsPureNash (fun a b => payoff P a b) (fun a b => payoff P b a) x y

/-- ADX1's revenue: a share `φ` of the price `w` of each of the `τ (1 + η₂)` impressions sold on ADX1
    to each advertiser bidding on it (proof of Proposition 7, p. 30). -/
def revenue (P : Params) (x y : AdDataSharing.Base.Exchange) : ℝ :=
  P.φ * P.w * ((if x = .adx1 then P.τ * (1 + P.η₂) else 0) +
    (if y = .adx1 then P.τ * (1 + P.η₂) else 0))

/-- w₁ = ((1 + η₂) − σ(1 − α)) C / (τ(1 + η₂) − σ(1 − α)) (proof of Proposition 5, p. 29). -/
noncomputable def w₁ (P : Params) : ℝ :=
  ((1 + P.η₂) - P.σ * (1 - P.α)) * P.C / (P.τ * (1 + P.η₂) - P.σ * (1 - P.α))

/-- w₂ = ([(1 + η₂) − σ] M + ασC) / (τ(1 + η₂) − σ(1 − α)) (proof of Proposition 5, p. 30). -/
noncomputable def w₂ (P : Params) : ℝ :=
  (((1 + P.η₂) - P.σ) * P.M + P.α * P.σ * P.C) / (P.τ * (1 + P.η₂) - P.σ * (1 - P.α))

/-- The accuracy threshold τ̃ of Proposition 5, **corrected**: the value of τ at which w = w₁,
    τ̃ = ((1 + η₂) − σ(1 − α)) C / (w (1 + η₂)) + σ(1 − α)/(1 + η₂). The printed display (6), p. 17,
    lacks the factor 1/(1 + η₂) on the first term. -/
noncomputable def tauTilde (P : Params) : ℝ :=
  ((1 + P.η₂) - P.σ * (1 - P.α)) * P.C / (P.w * (1 + P.η₂)) + P.σ * (1 - P.α) / (1 + P.η₂)

end AdDataSharing.Topics


