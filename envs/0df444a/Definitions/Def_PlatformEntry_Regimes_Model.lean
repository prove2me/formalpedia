-- Prove2me | Definitions.Def_PlatformEntry_Regimes_Model
-- name    : PlatformEntry_Regimes_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T01:22:09.577683+00:00
-- url     : https://prove2.me/theorems/1cab95d7-2718-4478-84e5-a2b738e7bbd4
-- title:
--   §3–§4, (1)–(8), (11), PDF pp. 7–16, 32–35 — parameters, standing ranges, condition (5), H, Ω, the closed forms (6)–(7) and the stage-2 entry subgame
-- statement:
--   This file sets up the model of Qi, Song & Xiao, *Coopetition in Platform-Based Retailing: On the Platform’s Entry*, §3–§4.
--
--   **Parameters.** A third-party seller sells one product on a platform for two periods. The parameters are the degree of spillover $\delta$, the referral rate $f$, the competition intensity $\beta$, the seller's effort-cost coefficient $c_S$, the platform's fixed entry cost $K$ and the product base value $a$. The platform's effort-cost coefficient is normalized to $c_P = 1/2$. The standing ranges of §3 are
--   $$\delta \in [0,1], \qquad f \in [0,1), \qquad \beta \in [0,1];$$
--   they are bundled as the predicate $\mathrm{InBox}(\delta,f,\beta)$.
--
--   **Stage 1.** The seller chooses an effort $e_S$, which raises the product value to $a + e_S$ at cost $c_S e_S^2$, and a quantity $q_1$; the price is $p_1 = a + e_S - q_1$ and the seller's stage-1 profit is
--   $$\Pi^S_1 = q_1 p_1 (1-f) - c_S e_S^2 .$$
--   Write $A = a + e_S$ for the value carried into stage 2.
--
--   **Stage 2 without entry.** The seller alone chooses $q_S$, the price is $p_S = A - q_S$, and the seller earns (1): $\Pi^S_{2,N} = q_S p_S (1-f)$.
--
--   **Stage 2 after entry.** The platform chooses an effort $e_P \ge 0$ at cost $e_P^2/2$. Then the seller and the platform choose quantities $q_S, q_P \ge 0$ simultaneously, with prices
--   $$p_S = A + \delta e_P - q_S - \beta q_P, \qquad p_P = A + e_P - q_P - \beta q_S,$$
--   and profits (3) and (4):
--   $$\Pi^S_{2,E} = q_S p_S (1-f), \qquad \Pi^P_{2,E} = q_S p_S f + q_P p_P - \tfrac12 e_P^2 - K .$$
--   A **quantity equilibrium** given $e_P$ is a pure Nash equilibrium of this quantity game over nonnegative quantities. An **entry equilibrium** is a triple $(e_P, q_S, q_P)$ with $e_P \ge 0$, $(q_S,q_P)$ a quantity equilibrium given $e_P$, and such that no other effort $e_P' \ge 0$, followed by any quantity equilibrium given $e_P'$, yields the platform a higher profit (4).
--
--   **The paper's closed forms.** With
--   $$N_5 = 4(1+\delta) - 2\beta(2-\delta+\delta^2) + \beta^3(1+f) - \beta^2(2+f+\delta f),$$
--   $$D = 8 - 8\delta^2 f + 8\beta\delta(1+f) - 2\beta^3\delta f(1+f) + \beta^4(1+f)^2 + 2\beta^2(-4-3f+\delta^2(-1+f^2)),$$
--   condition (5) is $N_5 > 0$, the numerator of $e^*_P/(a+e_S)$ in Lemma 2 is
--   $$8 + 8\delta f - 4\beta(1+\delta)(1+f) + \beta^3(1+\delta)f(1+f) - 2\beta^2(f+\delta(-1+f^2)),$$
--   and (8) is
--   $$H = \begin{cases} N_5^2 / D^2 & \text{if (5) holds},\\ 0 & \text{otherwise.}\end{cases}$$
--   The receptive regime is $\Omega = \{(\delta,f,\beta) \mid H > 1/4\}$. The seller's two-stage profits (6) and (7) are
--   $$\Pi^S_N(e_S) = \frac{(1-f)(a+e_S)^2}{2} - c_S e_S^2, \qquad \Pi^S_E(e_S) = \Big(\frac14 + H\Big)(1-f)(a+e_S)^2 - c_S e_S^2 .$$
--   The file also records the function (11) of Lemma 3,
--   $$P_{11} = -\beta^4(1+f)^2 + 8\delta(1+\delta f) + 2\beta^3(1+f)(1+\delta f) - 4\beta(2+\delta+\delta^2+2\delta f) + \beta^2(-2\delta f + 4(1+f) - 2\delta^2(-1+f^2)),$$
--   and the second factor of $\mathrm{Num}(f,\beta,\delta)$ in the proof of Proposition 2,
--   $$S_2 = \beta^4(1+f)^2 - 2\beta^3(1+f)(-1+\delta f) + 8(2+\delta-\delta^2 f) - 4\beta(2+\delta^2-\delta(3+2f)) + 2\beta^2(-6-4f-\delta f+\delta^2(-1+f^2)).$$
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Every polynomial is written term for term as printed. The parameters are explicit real arguments, not a structure, because the threshold results vary one of $\delta, f, \beta$ with the other two fixed. $H$ keeps the `if` of (8): an unconditional quotient would give $H = 1$ at $(\delta,f,\beta) = (0,0,1)$, where (5) fails. The two-stage profits $\Pi^S_N$, $\Pi^S_E$ take $\delta$ and $\beta$ as arguments for a common signature, although (6) does not use them. The platform's effort is restricted to $e_P \ge 0$; the seller's effort $e_S$ is any real number, as in the paper. The quantity equilibrium is the general two-player pure Nash equilibrium `CompetingChains.Cournot.IsPureNash` (a published definition), with both strategy sets equal to $[0,\infty)$.
-- source:
--   Qi, Song & Xiao, Coopetition in Platform-Based Retailing: On the Platform’s Entry, authors' manuscript with Online Supplement (2024-08-03; Management Science DOI 10.1287/mnsc.2023.00260), PDF pp. 7–10 (§3, (1), (3), (4)), p. 12 (Lemma 2, (5)), p. 15 ((6)–(8), Ω), Online Supplement PDF p. 32 (Lemma 3, (11)) and p. 35 (proof of Proposition 2)

import Mathlib
import Definitions.Def_CompetingChains_Cournot_TwoPlayerGame

namespace PlatformEntry.Regimes

/-! Qi, Song & Xiao, *Coopetition in Platform-Based Retailing: On the Platform's Entry*, §3–§4.
Parameters: spillover `δ`, referral rate `f`, competition intensity `β`, the seller's effort-cost
coefficient `cS`, the platform's entry cost `K`, the product base value `a`. The platform's effort-cost
coefficient is normalized to `c_P = 1/2` (p. 10) and appears as the literal `/ 2`. -/

/-- Standing ranges of §3 (pp. 8–9): `δ ∈ [0,1]`, `f ∈ [0,1)`, `β ∈ [0,1]`. -/
def InBox (δ f β : ℝ) : Prop := 0 ≤ δ ∧ δ ≤ 1 ∧ 0 ≤ f ∧ f < 1 ∧ 0 ≤ β ∧ β ≤ 1

/-- Left-hand side of condition (5), p. 12. -/
def N5 (δ f β : ℝ) : ℝ :=
  4 * (1 + δ) - 2 * β * (2 - δ + δ ^ 2) + β ^ 3 * (1 + f) - β ^ 2 * (2 + f + δ * f)

/-- Condition (5), p. 12: `4(1+δ) − 2β(2−δ+δ²) + β³(1+f) − β²(2+f+δf) > 0`. -/
def cond5 (δ f β : ℝ) : Prop := 0 < N5 δ f β

/-- Denominator of `e*_P` (Lemma 2, p. 12) and of `H` (8), p. 15. -/
def D (δ f β : ℝ) : ℝ :=
  8 - 8 * δ ^ 2 * f + 8 * β * δ * (1 + f) - 2 * β ^ 3 * δ * f * (1 + f) + β ^ 4 * (1 + f) ^ 2
    + 2 * β ^ 2 * (-4 - 3 * f + δ ^ 2 * (-1 + f ^ 2))

/-- Numerator of `e*_P / (a + e_S)` (Lemma 2, p. 12). -/
def ePNum (δ f β : ℝ) : ℝ :=
  8 + 8 * δ * f - 4 * β * (1 + δ) * (1 + f) + β ^ 3 * (1 + δ) * f * (1 + f)
    - 2 * β ^ 2 * (f + δ * (-1 + f ^ 2))

/-- `H` of (8), p. 15: `N5² / D²` if condition (5) holds, and `0` otherwise. -/
noncomputable def H (δ f β : ℝ) : ℝ := by
  classical exact if cond5 δ f β then N5 δ f β ^ 2 / D δ f β ^ 2 else 0

/-- `(δ, f, β) ∈ Ω`, where `Ω = {(δ,f,β) | H > 1/4}` (p. 15): the receptive regime. -/
def Omega (δ f β : ℝ) : Prop := 1 / 4 < H δ f β

/-- The function (11), Lemma 3, Online Supplement p. 32. -/
def P11 (δ f β : ℝ) : ℝ :=
  -β ^ 4 * (1 + f) ^ 2 + 8 * δ * (1 + δ * f) + 2 * β ^ 3 * (1 + f) * (1 + δ * f)
    - 4 * β * (2 + δ + δ ^ 2 + 2 * δ * f)
    + β ^ 2 * (-2 * δ * f + 4 * (1 + f) - 2 * δ ^ 2 * (-1 + f ^ 2))

/-- The second factor of `Num(f,β,δ)` in the proof of Proposition 2, Online Supplement p. 35. -/
def S2 (δ f β : ℝ) : ℝ :=
  β ^ 4 * (1 + f) ^ 2 - 2 * β ^ 3 * (1 + f) * (-1 + δ * f) + 8 * (2 + δ - δ ^ 2 * f)
    - 4 * β * (2 + δ ^ 2 - δ * (3 + 2 * f))
    + 2 * β ^ 2 * (-6 - 4 * f - δ * f + δ ^ 2 * (-1 + f ^ 2))

/-- (6), p. 15: the seller's two-stage profit under non-entry, as a function of the effort `e = e_S`.
(`δ` and `β` do not occur; they are kept so that (6) and (7) share one signature.) -/
noncomputable def profitN (δ f β cS a e : ℝ) : ℝ := (1 - f) * (a + e) ^ 2 / 2 - cS * e ^ 2

/-- (7), p. 15: the seller's two-stage profit under entry, as a function of the effort `e = e_S`. -/
noncomputable def profitE (δ f β cS a e : ℝ) : ℝ :=
  (1 / 4 + H δ f β) * (1 - f) * (a + e) ^ 2 - cS * e ^ 2

/-! Stage 1 and the stage-2 games (pp. 7–10). `A` stands for the carried-over value `a + e_S`. -/

/-- The seller's stage-1 profit `Π^S_1 = q₁ p₁ (1 − f) − c_S e_S²` with `p₁ = a + e_S − q₁` (pp. 7–8). -/
def stage1Seller (f cS a eS q₁ : ℝ) : ℝ := q₁ * (a + eS - q₁) * (1 - f) - cS * eS ^ 2

/-- (1): the seller's stage-2 profit without entry, `q_S p_S (1 − f)` with `p_S = A − q_S` (p. 8). -/
def stage2SellerN (f A qS : ℝ) : ℝ := qS * (A - qS) * (1 - f)

/-- The seller's price after entry, `p_S = A + δ e_P − q_S − β q_P` (p. 9). -/
def priceS (δ β A eP qS qP : ℝ) : ℝ := A + δ * eP - qS - β * qP

/-- The platform's price after entry, `p_P = A + e_P − q_P − β q_S` (p. 9). -/
def priceP (β A eP qS qP : ℝ) : ℝ := A + eP - qP - β * qS

/-- (3), p. 10: the seller's stage-2 profit after entry, `Π^S_{2,E} = q_S p_S (1 − f)`. -/
def sellerPayoffE (δ f β A eP qS qP : ℝ) : ℝ := qS * priceS δ β A eP qS qP * (1 - f)

/-- (4), p. 10, with `C_P(e_P) = e_P²/2`: the platform's stage-2 profit after entry,
`Π^P_{2,E} = q_S p_S f + q_P p_P − e_P²/2 − K`. -/
noncomputable def platformPayoffE (δ f β K A eP qS qP : ℝ) : ℝ :=
  qS * priceS δ β A eP qS qP * f + qP * priceP β A eP qS qP - eP ^ 2 / 2 - K

/-- Cournot equilibrium of the stage-2 quantity game after entry, given the platform's effort `e_P`:
`q_S, q_P ≥ 0`, and `(q_S, q_P)` is a pure Nash equilibrium (`CompetingChains.Cournot.IsPureNash`) of the
two-player game in which both parties choose quantities in `[0, ∞)`, with payoffs (3) (seller) and (4)
(platform). -/
def IsQuantityEq (δ f β K A eP qS qP : ℝ) : Prop :=
  ∃ (hS : 0 ≤ qS) (hP : 0 ≤ qP),
    CompetingChains.Cournot.IsPureNash (A₁ := {x : ℝ // 0 ≤ x}) (A₂ := {x : ℝ // 0 ≤ x})
      (fun x y => sellerPayoffE δ f β A eP x.1 y.1)
      (fun x y => platformPayoffE δ f β K A eP x.1 y.1) ⟨qS, hS⟩ ⟨qP, hP⟩

/-- Subgame-perfect outcome of stage 2 after entry: the platform's effort `e_P ≥ 0` together with a
quantity equilibrium after it, such that no effort `e_P' ≥ 0` followed by any quantity equilibrium gives
the platform a higher profit (4). -/
def IsEntryEq (δ f β K A eP qS qP : ℝ) : Prop :=
  0 ≤ eP ∧ IsQuantityEq δ f β K A eP qS qP ∧
  ∀ eP' qS' qP' : ℝ, 0 ≤ eP' → IsQuantityEq δ f β K A eP' qS' qP' →
    platformPayoffE δ f β K A eP' qS' qP' ≤ platformPayoffE δ f β K A eP qS qP

end PlatformEntry.Regimes


