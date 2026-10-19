-- Prove2me | Definitions.Def_PriceMatchNeg_Symmetric_Model
-- name    : PriceMatchNeg_Symmetric_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:12.76447+00:00
-- url     : https://prove2.me/theorems/9168e5c8-e458-4da7-99c1-0abdd49b2a54
-- title:
--   §2–§3.2, pp. 7–10 — common-seller two-buyer negotiation game: Bertrand retail stage, Nash-bargained wholesale prices under SN and PM
-- statement:
--   This file defines the common-seller, two-buyer supply chain of Shang and Cai and its two wholesale-price negotiation mechanisms, **simultaneous negotiation (SN)** and **price matching (PM)**.
--
--   **Market.** A seller supplies an intermediate good to Buyers $1$ and $2$, who turn it one-for-one into substitutable end products. With demand base $a > 0$ and substitutability $\gamma \in [0,1)$, the reverse demand system $p_i = a - x_i - \gamma x_j$ ($j = 3-i$) inverts to the demand
--
--   $$x_i(p_i, p_j) = \frac{(1-\gamma)a - p_i + \gamma p_j}{1-\gamma^2}.$$
--
--   **Second stage.** Given wholesale prices $(w_i, w_j)$, Buyer $i$ earns $(p_i - w_i)\,x_i(p_i,p_j)$ and the buyers compete in retail prices (a Bertrand equilibrium is a pair of mutual best responses). The paper's equilibrium prices and quantities are
--
--   $$\hat p_i(w_i,w_j) = \frac{(2-\gamma-\gamma^2)a + 2w_i + \gamma w_j}{4-\gamma^2}, \qquad \hat x_i(w_i,w_j) = \frac{(2-\gamma-\gamma^2)a - (2-\gamma^2)w_i + \gamma w_j}{(1-\gamma^2)(4-\gamma^2)}.$$
--
--   The second-stage profits $\pi_i(w_i,w_j)$ and $\pi_s(w_i,w_j) = w_i x_i + w_j x_j$ are defined by evaluating the primitive profit expressions at $(\hat p_i, \hat p_j)$.
--
--   **Monopoly fallback.** If only Buyer $j$ trades, its demand is $a - p_j$, it charges $p^M_j = (a+w_j)/2$, and the profits are $\pi^M_j(w_j) = (p^M_j - w_j)(a - p^M_j)$ and $\pi^M_s(w_j) = w_j(a - p^M_j)$. The single-channel bargain $\hat w_j$ is a Nash bargaining solution with powers $(\theta_j, 1-\theta_j)$, payoffs $(\pi^M_j, \pi^M_s)$ and disagreement point $(0,0)$.
--
--   **SN.** A pair $(w_1, w_2) \in [0,a]^2$ is an SN equilibrium with powers $\theta_1, \theta_2 \in (0,1)$ if, for $i = 1,2$, $w_i$ is the Nash bargaining solution of dyad $i$ with payoffs $\pi_i(\cdot, w_j)$, $\pi_s(\cdot, w_j)$ and disagreement point $(0, \pi^M_s(w_j))$.
--
--   **PM.** The seller first negotiates with Buyer $i$; the other buyer accepts the same price. A price $w \in [0,a]$ is a PM equilibrium price if it is the Nash bargaining solution with powers $(\theta_i, 1-\theta_i)$, payoffs $\pi_i(w,w)$, $\pi_s(w,w)$ and disagreement point $(0, \pi^M_s(\hat w_j))$.
--
--   Finally the file records the paper's closed forms
--
--   $$w^{SN} = \frac{(1-\theta)(1-\gamma)(2+\gamma)a}{2(1-\gamma)(2+\gamma) + \gamma^2(1+\gamma)(2-\gamma)\theta}, \qquad w^{PM}_i = \frac{\Bigl(3 - \theta_i - \sqrt{1 - \gamma\theta_i + \gamma^2\theta_i + \theta_i^2 + (1+\gamma)(2-\gamma)\theta_i\theta_j^2}\Bigr)a}{4},$$
--
--   which only the milestones use.
--
--   **Formalization Note** The sign $a > 0$ is added (the paper never states it). Equilibrium wholesale prices are required to lie in $[0,a]$, the paper's "entire feasible domain" (p. 9; Online Supplement p. 1, "$0 \le w_i \le a$"); bargaining deviations range over all individually rational $w \ge 0$. In PM the matched price applies to both buyers (the paper's "Buyer $j$ would accept", p. 9, is taken as a modeling convention). The profits are defined from the demand system, not by the closed forms (1)–(2), which are milestones; $\pi^M_j, \pi^M_s$ are defined at the closed-form monopoly price, whose optimality is a milestone. All quantities are real numbers.
-- source:
--   Shang & Cai, Implications of Price Matching in Supply Chain Negotiation, accepted manuscript (MSOM, forthcoming; SSRN 3021563), pp. 7–10 (PDF 7–10), §2, §3.1.1, §3.1.2, §3.2.1, §3.2.2

import Mathlib
import Definitions.Def_PriceMatchNeg_Symmetric_NashBargain

namespace PriceMatchNeg.Symmetric

/-- Market parameters (§2, p. 7): the buyers' demand base `a` and the product substitutability `γ`. -/
structure Params where
  /-- the buyers' initial demand base -/
  a : ℝ
  /-- product substitutability -/
  γ : ℝ

/-- Standing assumptions of §2 (p. 7): `γ ∈ [0, 1)`, and a positive demand base `a > 0` (the sign of `a`
is not stated in the paper; it is added). -/
def Params.Standing (P : Params) : Prop := 0 < P.a ∧ 0 ≤ P.γ ∧ P.γ < 1

/-- A bargaining power `θ ∈ (0, 1)` (§2, p. 7). -/
def ValidPower (θ : ℝ) : Prop := 0 < θ ∧ θ < 1

/-! ### Second stage: differentiated Bertrand competition (§2, p. 7; §3.1.1, p. 8) -/

/-- Buyer `i`'s demand `x_i(p_i, p_j)` at retail prices `(p_i, p_j)`, obtained by inverting the reverse
demand system `p_i = a − x_i − γ x_j`, `p_j = a − x_j − γ x_i` (p. 7). -/
noncomputable def demand (P : Params) (pi pj : ℝ) : ℝ :=
  ((1 - P.γ) * P.a - pi + P.γ * pj) / (1 - P.γ ^ 2)

/-- Buyer `i`'s profit `π_i = (p_i − w_i) x_i(p_i, p_j)` at wholesale price `w_i` (p. 8). -/
noncomputable def retailProfit (P : Params) (wi pi pj : ℝ) : ℝ := (pi - wi) * demand P pi pj

/-- `(p_i, p_j)` is a Bertrand (Nash) equilibrium of the retail-price game at wholesale prices
`(w_i, w_j)`: each buyer's retail price is a best response to the other's. -/
def IsBertrandEq (P : Params) (wi wj pi pj : ℝ) : Prop :=
  (∀ p, retailProfit P wi p pj ≤ retailProfit P wi pi pj) ∧
  (∀ p, retailProfit P wj p pi ≤ retailProfit P wj pj pi)

/-- The equilibrium retail price `p̂_i(w_i, w_j) = ((2 − γ − γ²)a + 2w_i + γw_j)/(4 − γ²)` (p. 8). -/
noncomputable def pHat (P : Params) (wi wj : ℝ) : ℝ :=
  ((2 - P.γ - P.γ ^ 2) * P.a + 2 * wi + P.γ * wj) / (4 - P.γ ^ 2)

/-- The equilibrium sales quantity
`x̂_i(w_i, w_j) = ((2 − γ − γ²)a − (2 − γ²)w_i + γw_j)/((1 − γ²)(4 − γ²))` (p. 8). -/
noncomputable def xHat (P : Params) (wi wj : ℝ) : ℝ :=
  ((2 - P.γ - P.γ ^ 2) * P.a - (2 - P.γ ^ 2) * wi + P.γ * wj) / ((1 - P.γ ^ 2) * (4 - P.γ ^ 2))

/-- Buyer `i`'s second-stage equilibrium profit `π_i(w_i, w_j)`: its profit `(p_i − w_i) x_i(p_i, p_j)`
evaluated at the retail prices `p̂_i(w_i, w_j)`, `p̂_j(w_j, w_i)` (not the closed form (1)). -/
noncomputable def piB (P : Params) (wi wj : ℝ) : ℝ :=
  retailProfit P wi (pHat P wi wj) (pHat P wj wi)

/-- The seller's second-stage equilibrium profit `π_s(w_i, w_j) = w_i x_i(p_i, p_j) + w_j x_j(p_j, p_i)`
evaluated at the retail prices `p̂_i(w_i, w_j)`, `p̂_j(w_j, w_i)` (not the closed form (2)). -/
noncomputable def piS (P : Params) (wi wj : ℝ) : ℝ :=
  wi * demand P (pHat P wi wj) (pHat P wj wi) + wj * demand P (pHat P wj wi) (pHat P wi wj)

/-! ### Single-channel monopoly market (§3.1.2, p. 9) -/

/-- Buyer `j`'s profit `(p_j − w_j)(a − p_j)` when it is the only viable buyer (demand `x_j = a − p_j`). -/
def monoProfit (P : Params) (w p : ℝ) : ℝ := (p - w) * (P.a - p)

/-- The monopoly retail price `p^M_j = (a + w_j)/2` (p. 9). -/
noncomputable def pMono (P : Params) (w : ℝ) : ℝ := (P.a + w) / 2

/-- Buyer `j`'s monopoly profit `π^M_j(w_j)`: `monoProfit` at the monopoly price. -/
noncomputable def piMb (P : Params) (w : ℝ) : ℝ := monoProfit P w (pMono P w)

/-- The seller's monopoly profit `π^M_s(w_j) = w_j x_j(p^M_j) = w_j (a − p^M_j)`. -/
noncomputable def piMs (P : Params) (w : ℝ) : ℝ := w * (P.a - pMono P w)

/-! ### First stage: Nash-bargained wholesale prices (§3.2, pp. 9–10) -/

/-- `w` is the outcome `ŵ_j` of the single-channel bargain between the seller and buyer `j` (bargaining
power `θ_j`): it maximizes `[π^M_j(w)]^{θ_j} [π^M_s(w)]^{1−θ_j}`, disagreement point `(0, 0)` (p. 10). -/
def IsMonoBargain (P : Params) (θj w : ℝ) : Prop := IsNashBargain θj (piMb P) (piMs P) 0 w

/-- `(w_1, w_2)` is an equilibrium pair of simultaneous negotiation (SN, p. 9) with bargaining powers
`θ_1, θ_2`: both prices lie in the feasible domain `[0, a]`, and each `w_i` is the Nash bargaining
solution of dyad `i` given the other dyad's price `w_j`, with payoffs `π_i(·, w_j)`, `π_s(·, w_j)` and
disagreement point `(0, π^M_s(w_j))`. -/
def IsSNEq (P : Params) (θ1 θ2 w1 w2 : ℝ) : Prop :=
  w1 ∈ Set.Icc 0 P.a ∧ w2 ∈ Set.Icc 0 P.a ∧
  IsNashBargain θ1 (fun w => piB P w w2) (fun w => piS P w w2) (piMs P w2) w1 ∧
  IsNashBargain θ2 (fun w => piB P w w1) (fun w => piS P w w1) (piMs P w1) w2

/-- `w` is an equilibrium wholesale price of price-matching negotiation (PM, p. 10) when the seller first
negotiates with buyer `i` (bargaining power `θ_i`), the other buyer `j` having power `θ_j`: `w ∈ [0, a]`,
and `w` is the Nash bargaining solution with payoffs `π_i(w, w)`, `π_s(w, w)` (the matched price applies
to both buyers) and disagreement point `(0, π^M_s(ŵ_j))`, `ŵ_j` the single-channel bargain with buyer `j`. -/
def IsPMPrice (P : Params) (θi θj w : ℝ) : Prop :=
  w ∈ Set.Icc 0 P.a ∧ ∃ wh, IsMonoBargain P θj wh ∧
    IsNashBargain θi (fun v => piB P v v) (fun v => piS P v v) (piMs P wh) w

/-! ### The paper's closed forms (used only by the milestones) -/

/-- `w^SN = (1 − θ)(1 − γ)(2 + γ)a / (2(1 − γ)(2 + γ) + γ²(1 + γ)(2 − γ)θ)` (p. 9), symmetric power `θ`. -/
noncomputable def wSN (P : Params) (θ : ℝ) : ℝ :=
  (1 - θ) * (1 - P.γ) * (2 + P.γ) * P.a /
    (2 * (1 - P.γ) * (2 + P.γ) + P.γ ^ 2 * (1 + P.γ) * (2 - P.γ) * θ)

/-- `w^PM_i = (3 − θ_i − √(1 − γθ_i + γ²θ_i + θ_i² + (1 + γ)(2 − γ)θ_iθ_j²)) a/4` (p. 10). -/
noncomputable def wPM (P : Params) (θi θj : ℝ) : ℝ :=
  (3 - θi - Real.sqrt (1 - P.γ * θi + P.γ ^ 2 * θi + θi ^ 2 + (1 + P.γ) * (2 - P.γ) * θi * θj ^ 2)) *
    P.a / 4

end PriceMatchNeg.Symmetric


