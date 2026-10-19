-- Prove2me | Definitions.Def_SharingPlatform_WageSchemes_Model
-- name    : SharingPlatform_WageSchemes_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:20.57803+00:00
-- url     : https://prove2.me/theorems/1acdfa36-be71-4d08-8ef9-b1c9cb2f8810
-- title:
--   §3–§4.1, pp. 7–12 (PDF 8–13) — two-sided platform duopoly: linear demand and supply, transaction volume, DCR game, FCR and FW two-stage games, closed forms (4)–(9), (39), (44), (13), (66)
-- statement:
--   The model of Zhang, Chen and Raghunathan's two-sided platform duopoly, and the closed-form quantities their equilibrium analysis produces.
--
--   **Parameters.** A market is described by six real numbers $a, b, c, k, l, m$. The *standing assumptions* are that all six are strictly positive, together with
--
--   $$\text{Assumption 1: } \frac{a}{c} > \frac{k}{m}, \qquad \text{Assumption 2: } l \le 2c + \frac{c^2}{b}.$$
--
--   **Demand, supply, profit.** Two platforms $i \in \{1,2\}$ (with $\bar i = 3 - i$) each set a consumer price $p_i$ and pay workers a wage $w_i$ per transaction. Demand and worker supply on platform $i$ are
--
--   $$d_i = a - b(p_i - p_{\bar i}) - c\,p_i, \qquad s_i = -k + l(w_i - w_{\bar i}) + m\,w_i,$$
--
--   the transaction volume is $\max\{0, \min\{d_i, s_i\}\}$, and platform $i$'s profit is $\pi_i = (p_i - w_i)\max\{0,\min\{d_i, s_i\}\}$.
--
--   **Three wage schemes.**
--   1. *Dynamic commission rate (DCR)*: a one-shot game in which each platform chooses a price $p_i$ and a commission rate $\alpha_i$ (both real), the wage being $w_i = (1-\alpha_i)p_i$, so that $\pi_i = \alpha_i p_i \max\{0,\min\{d_i,s_i\}\}$. A Nash equilibrium is a pair of actions each of which maximizes its platform's profit over all of $\mathbb R^2$ against the other.
--   2. *Fixed commission rate (FCR)*: in stage 1 each platform announces $\alpha_i \in \mathbb R$; in stage 2, having seen both, it chooses $p_i$; the wage is $(1-\alpha_i)p_i$.
--   3. *Fixed wage (FW)*: in stage 1 each platform announces $w_i \in \mathbb R$; in stage 2 it chooses $p_i$.
--
--   A strategy profile of a two-stage game consists of stage-1 actions $x_1, x_2$ and stage-2 price rules $P_1, P_2 : \mathbb R^2 \to \mathbb R$ giving each platform's price after any stage-1 pair. It is a *subgame-perfect equilibrium* if (i) after every stage-1 pair $(y_1,y_2)$ the prices $(P_1(y_1,y_2), P_2(y_1,y_2))$ are a Nash equilibrium of the pricing game, and (ii) no platform gains by changing its stage-1 action, prices following the rules at the changed pair. A profile is *symmetric* if $x_1 = x_2$ and the two on-path prices coincide, and *non-trivial* if on-path demand and supply are positive on both platforms. For DCR, a symmetric profile is a pair $(x, x)$, and non-triviality has the same meaning.
--
--   **Closed forms.** The definition file also names the paper's formulas: the DCR price $p^{D*}$ (4) and commission rate $\alpha^{D*}$ (5); the threshold $\bar\alpha = 1 - \frac{a(b+c)+k(b+2c)}{am}$ (39); the quadratic $f(\alpha) = A\alpha^2 + B\alpha + C$ of (44); equation (6) and the FCR price $p^{F}(\alpha) = \frac{a+k}{c + m(1-\alpha)}$ (7); the FW wage $w^{W*}$ (8) and price $p^{W*} = \frac{a + k - m w^{W*}}{c}$ (9); $\alpha^{W*} = 1 - w^{W*}/p^{W*}$; the left side of Inequality (13),
--   $$\frac{b+c+l+m}{(b+c)(l+m)\alpha} - \frac{b + (1-\alpha)l}{(1-\alpha)(cl - bm)};$$
--   the profit-as-a-function-of-price $\Pi(p) = \left(\frac{m+c}{m}p - \frac{a+k}{m}\right)(a - cp)$ of (66), and $\hat p = \frac{(m+c)a + c(a+k)}{2c(m+c)}$, the zero of $\Pi'$.
--
--   These objects are the vocabulary of every statement in the mission.
--
--   **Formalization Note** (1) $\mathbb R^+$ is read as strictly positive. (2) The paper writes the volume as $\min\{d_i,s_i\}$; with negative values allowed, the profit is unbounded above (a negative price with a negative wage makes both factors negative), so no equilibrium would exist. The volume is truncated at $0$. (3) The paper does not write out the strategies of its two-stage games; the stage-2 prices are functions of the full stage-1 pair, as subgame perfection requires. (4) `OnPathContinuous` says that both stage-2 price rules are continuous at the equilibrium stage-1 pair. It is a regularity condition used by the theorems, not part of `IsSPE`; see those statements. (5) `cond13` and `Eq6` contain real divisions; every statement that uses them either proves or assumes their denominators nonzero.
-- source:
--   Zhang, Chen, Raghunathan, Two-Sided Platform Competition in a Sharing Economy, SSRN 3555993, pp. 7–12 (PDF 8–13), §3, §4.1, Equations (1)–(9), Assumptions 1–2; Appendix A.4 (39), (44), p. 40 and p. 43 (PDF 41, 44); A.7–A.8 (66), pp. 51–52 (PDF 52–53); Proposition 3 (13), p. 17 (PDF 18)

import Mathlib

namespace SharingPlatform.WageSchemes

/-- The six market parameters of §3 (pp. 7–8): demand intercept `a`, demand-side substitutability
`b`, loyal-consumer price sensitivity `c`, supply threshold `k`, supply-side substitutability `l`,
loyal-worker wage sensitivity `m`. -/
structure Params where
  a : ℝ
  b : ℝ
  c : ℝ
  k : ℝ
  l : ℝ
  m : ℝ

/-- Standing assumptions (pp. 7–9): `a, b, c, k, l, m ∈ ℝ⁺` (read as strictly positive),
Assumption 1 `a/c > k/m`, and Assumption 2 `l ≤ 2c + c²/b`. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.a ∧ 0 < P.b ∧ 0 < P.c ∧ 0 < P.k ∧ 0 < P.l ∧ 0 < P.m ∧
  P.k / P.m < P.a / P.c ∧ P.l ≤ 2 * P.c + P.c ^ 2 / P.b

/-- Equation (1): demand of a platform charging price `p` when the rival charges `q`. -/
def demand (P : Params) (p q : ℝ) : ℝ := P.a - P.b * (p - q) - P.c * p

/-- Equation (2): worker supply of a platform offering wage `w` when the rival offers `v`. -/
def supply (P : Params) (w v : ℝ) : ℝ := -P.k + P.l * (w - v) + P.m * w

/-- Transaction volume `min {d, s}`, truncated at `0` (no negative transactions). -/
def volume (d s : ℝ) : ℝ := max 0 (min d s)

/-- Equation (3): profit of a platform with own price `p` and wage `w` against a rival with
price `q` and wage `v`. -/
def profit (P : Params) (p w q v : ℝ) : ℝ :=
  (p - w) * volume (demand P p q) (supply P w v)

/-! ### Dynamic commission rate (DCR): a one-shot game in (price, commission rate) -/

/-- The wage `(1 - α) p` paid under the DCR action `x = (p, α)`. -/
def dcrWage (x : ℝ × ℝ) : ℝ := (1 - x.2) * x.1

/-- DCR profit of a platform playing `x = (p, α)` against a rival playing `y`; it equals
`α p · volume`. -/
def profitDCR (P : Params) (x y : ℝ × ℝ) : ℝ := profit P x.1 (dcrWage x) y.1 (dcrWage y)

/-- `(x₁, x₂)` is a pure-strategy Nash equilibrium of the DCR game: each action maximizes its
platform's profit over all (price, commission rate) pairs against the other's action. -/
def IsNashDCR (P : Params) (x₁ x₂ : ℝ × ℝ) : Prop :=
  (∀ y : ℝ × ℝ, profitDCR P y x₂ ≤ profitDCR P x₁ x₂) ∧
  (∀ y : ℝ × ℝ, profitDCR P y x₁ ≤ profitDCR P x₂ x₁)

/-- Positive demand and supply on both platforms at the DCR profile `(x₁, x₂)` (p. 9). -/
def NontrivialDCR (P : Params) (x₁ x₂ : ℝ × ℝ) : Prop :=
  0 < demand P x₁.1 x₂.1 ∧ 0 < supply P (dcrWage x₁) (dcrWage x₂) ∧
  0 < demand P x₂.1 x₁.1 ∧ 0 < supply P (dcrWage x₂) (dcrWage x₁)

/-! ### Two-stage games: fixed commission rate (FCR) and fixed wage (FW) -/

/-- FCR wage rule: stage-1 commission rate `x`, price `p`, wage `(1 - x) p`. -/
def fcrWage (x p : ℝ) : ℝ := (1 - x) * p

/-- FW wage rule: stage-1 wage `x`, independent of the price. -/
def fwWage (x _p : ℝ) : ℝ := x

/-- A strategy profile of a two-stage game: stage-1 actions `x₁, x₂` (commission rates or wages)
and, for each platform, its stage-2 price as a function of the stage-1 pair `(y₁, y₂)`. -/
structure TwoStage where
  x₁ : ℝ
  x₂ : ℝ
  P₁ : ℝ → ℝ → ℝ
  P₂ : ℝ → ℝ → ℝ

/-- In the pricing subgame after stage-1 actions `(y₁, y₂)` under wage rule `W`, the prices
`(p₁, p₂)` form a Nash equilibrium. -/
def IsPricingNash (P : Params) (W : ℝ → ℝ → ℝ) (y₁ y₂ p₁ p₂ : ℝ) : Prop :=
  (∀ p : ℝ, profit P p (W y₁ p) p₂ (W y₂ p₂) ≤ profit P p₁ (W y₁ p₁) p₂ (W y₂ p₂)) ∧
  (∀ p : ℝ, profit P p (W y₂ p) p₁ (W y₁ p₁) ≤ profit P p₂ (W y₂ p₂) p₁ (W y₁ p₁))

/-- Platform 1's profit under profile `e` when the stage-1 actions are `(y₁, y₂)`. -/
def TwoStage.profit₁ (P : Params) (W : ℝ → ℝ → ℝ) (e : TwoStage) (y₁ y₂ : ℝ) : ℝ :=
  profit P (e.P₁ y₁ y₂) (W y₁ (e.P₁ y₁ y₂)) (e.P₂ y₁ y₂) (W y₂ (e.P₂ y₁ y₂))

/-- Platform 2's profit under profile `e` when the stage-1 actions are `(y₁, y₂)`. -/
def TwoStage.profit₂ (P : Params) (W : ℝ → ℝ → ℝ) (e : TwoStage) (y₁ y₂ : ℝ) : ℝ :=
  profit P (e.P₂ y₁ y₂) (W y₂ (e.P₂ y₁ y₂)) (e.P₁ y₁ y₂) (W y₁ (e.P₁ y₁ y₂))

/-- Subgame-perfect equilibrium: (i) in every pricing subgame `(y₁, y₂)` the stage-2 prices are
a Nash equilibrium; (ii) no platform gains by a stage-1 deviation, the prices following the
profile's stage-2 rule at the deviated pair. -/
def IsSPE (P : Params) (W : ℝ → ℝ → ℝ) (e : TwoStage) : Prop :=
  (∀ y₁ y₂ : ℝ, IsPricingNash P W y₁ y₂ (e.P₁ y₁ y₂) (e.P₂ y₁ y₂)) ∧
  (∀ y : ℝ, e.profit₁ P W y e.x₂ ≤ e.profit₁ P W e.x₁ e.x₂) ∧
  (∀ y : ℝ, e.profit₂ P W e.x₁ y ≤ e.profit₂ P W e.x₁ e.x₂)

/-- Regularity of the stage-2 rule on the equilibrium path: both price functions are
continuous at the equilibrium stage-1 pair (the appendix differentiates the subgame prices
(40) and (50) with respect to the stage-1 actions there). -/
def TwoStage.OnPathContinuous (e : TwoStage) : Prop :=
  ContinuousAt (Function.uncurry e.P₁) (e.x₁, e.x₂) ∧
  ContinuousAt (Function.uncurry e.P₂) (e.x₁, e.x₂)

/-- Symmetric: equal stage-1 actions and equal on-path prices (off-path behaviour is free). -/
def TwoStage.IsSymmetric (e : TwoStage) : Prop :=
  e.x₁ = e.x₂ ∧ e.P₁ e.x₁ e.x₂ = e.P₂ e.x₁ e.x₂

/-- Positive on-path demand and supply on both platforms (p. 9). -/
def TwoStage.Nontrivial (P : Params) (W : ℝ → ℝ → ℝ) (e : TwoStage) : Prop :=
  0 < demand P (e.P₁ e.x₁ e.x₂) (e.P₂ e.x₁ e.x₂) ∧
  0 < supply P (W e.x₁ (e.P₁ e.x₁ e.x₂)) (W e.x₂ (e.P₂ e.x₁ e.x₂)) ∧
  0 < demand P (e.P₂ e.x₁ e.x₂) (e.P₁ e.x₁ e.x₂) ∧
  0 < supply P (W e.x₂ (e.P₂ e.x₁ e.x₂)) (W e.x₁ (e.P₁ e.x₁ e.x₂))

/-- On-path (equilibrium) profit of platform 1 in a two-stage profile. -/
def TwoStage.onPathProfit (P : Params) (W : ℝ → ℝ → ℝ) (e : TwoStage) : ℝ :=
  e.profit₁ P W e.x₁ e.x₂

/-! ### Closed forms and auxiliary quantities of the paper -/

/-- Equation (4): the DCR equilibrium price. -/
noncomputable def pD (P : Params) : ℝ :=
  (P.k * (P.b + P.c) * (P.l + P.m) +
      P.a * (P.m * (P.l + P.m) + (P.b + P.c) * (P.l + 2 * P.m))) /
    (P.c * (P.b + P.c) * (P.l + 2 * P.m) + P.m * (P.b + 2 * P.c) * (P.l + P.m))

/-- Equation (5): the DCR equilibrium commission rate. -/
noncomputable def alphaD (P : Params) : ℝ :=
  (P.b + P.c + P.l + P.m) * (P.a * P.m - P.c * P.k) /
    (P.k * (P.b + P.c) * (P.l + P.m) +
      P.a * (P.m * (P.l + P.m) + (P.b + P.c) * (P.l + 2 * P.m)))

/-- Equation (39): the threshold `ᾱ`. -/
noncomputable def alphaBar (P : Params) : ℝ :=
  1 - (P.a * (P.b + P.c) + P.k * (P.b + 2 * P.c)) / (P.a * P.m)

/-- Equation (44): `f(α) = Aα² + Bα + C`. -/
def fFCR (P : Params) (α : ℝ) : ℝ :=
  (P.m * (P.a + P.k) * (P.b + P.c) * (2 * P.l + P.m) +
      P.a * P.m * (P.m * (P.b + 2 * P.l + P.m) + P.c * (P.l + P.m))) * α ^ 2 +
    (-(P.c + P.m) * (P.a * (2 * P.m * (2 * P.b + P.c + 2 * P.l) + P.l * (2 * P.b + P.c) +
        2 * P.m ^ 2) + P.b * P.k * (2 * P.l + P.m))) * α +
    (P.c + P.m) * (P.a * P.m - P.c * P.k) * (2 * P.b + P.c + 2 * P.l + P.m)

/-- Equation (6) at commission rate `α`, with its real divisions. -/
def Eq6 (P : Params) (α : ℝ) : Prop :=
  ((1 - α) * (P.m * (P.b + 2 * P.l + P.m) + P.c * (P.l + P.m)) + P.b * (2 * P.c + P.m) +
        P.c * (P.c + P.l + P.m)) /
      ((1 - α) * P.m * (P.b + P.c) * (2 * P.l + P.m) + P.c * (2 * P.b + P.c) * (P.l + P.m)) =
    α * (P.a + P.k) / (P.m * P.a * (1 - α) - P.c * P.k)

/-- Equation (7): the FCR equilibrium price as a function of the commission rate. -/
noncomputable def priceFCR (P : Params) (α : ℝ) : ℝ := (P.a + P.k) / (P.c + P.m * (1 - α))

/-- Equation (8): the FW equilibrium wage. -/
noncomputable def wW (P : Params) : ℝ :=
  (P.b * (2 * P.a * (P.l + P.m) + 2 * P.c * P.k + P.k * (2 * P.l + 3 * P.m)) +
      P.c * ((P.a + 2 * P.k) * (P.l + P.m) + P.c * P.k)) /
    (P.b * (2 * P.c * (P.l + 2 * P.m) + P.m * (2 * P.l + 3 * P.m)) +
      P.c * (P.c * (P.l + 2 * P.m) + 2 * P.m * (P.l + P.m)))

/-- Equation (9): the FW equilibrium price. -/
noncomputable def pW (P : Params) : ℝ := (P.a + P.k - P.m * wW P) / P.c

/-- The FW equilibrium commission rate `α^{W*} = 1 - w^{W*}/p^{W*}` (A.8, p. 52). -/
noncomputable def alphaW (P : Params) : ℝ := 1 - wW P / pW P

/-- The left side of Inequality (13) at commission rate `α`. -/
noncomputable def cond13 (P : Params) (α : ℝ) : ℝ :=
  (P.b + P.c + P.l + P.m) / ((P.b + P.c) * (P.l + P.m) * α) -
    (P.b + (1 - α) * P.l) / ((1 - α) * (P.c * P.l - P.b * P.m))

/-- Equation (66): equilibrium profit `((m + c)/m · p − (a + k)/m)(a − c p)` as a function of
the equilibrium price when demand equals supply. -/
noncomputable def profitAtPrice (P : Params) (p : ℝ) : ℝ :=
  ((P.m + P.c) / P.m * p - (P.a + P.k) / P.m) * (P.a - P.c * p)

/-- The zero of `∂π*/∂p* = (m+c)a/m + c(a+k)/m − 2c(m+c)p*/m` (A.8, p. 51). -/
noncomputable def pHat (P : Params) : ℝ :=
  ((P.m + P.c) * P.a + P.c * (P.a + P.k)) / (2 * P.c * (P.m + P.c))

end SharingPlatform.WageSchemes


