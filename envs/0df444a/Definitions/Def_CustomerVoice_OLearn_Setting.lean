-- Prove2me | Definitions.Def_CustomerVoice_OLearn_Setting
-- name    : CustomerVoice_OLearn_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T01:07:17.443869+00:00
-- url     : https://prove2.me/theorems/2a44c843-7c95-4f51-a76a-ee40f24d8df9
-- title:
--   §2 and §3.3 — the two-type customization model and the O-Learning self-design game: payoff (9), seller acceptance, separating equilibria, q*(θ), thresholds ΛH1, ΛH2, ΛL, Λ
-- statement:
--   This file sets up the O-Learning ("self-design") game of Guo, *The Voice of Customers in Customization*.
--
--   **Primitives (§2).** A seller customizes products of quality $q \ge 0$ for buyers. A buyer's quality preference is $\theta \in \{\theta_H, \theta_L\}$ (the two buyer types $H$ and $L$), privately known to the buyer, with prior probability $\alpha$ of the high type. Producing quality $q$ costs $kq^2$ and selling it costs $sq^2$. In the price stage the seller makes a take-it-or-leave-it offer with probability $\gamma$ and the buyer does with probability $1-\gamma$. The standing assumptions are
--   $$\theta_H > \theta_L > 0,\qquad \alpha \in (0,1),\qquad \gamma\in(0,1),\qquad k>0,\qquad s>0.$$
--
--   **Payoffs.** A buyer with true preference $\theta$ whom the seller believes to be $\hat\theta$ and whose request $q$ is accepted expects (9)
--   $$\mu(q,\theta,\hat\theta) = \gamma\max\{\theta q-\hat\theta q,0\} + (1-\gamma)\max\{\theta q-kq^2,0\}.$$
--   The seller accepts a request $q$ from a buyer believed to be $\hat\theta$ if and only if $\gamma(\hat\theta q - kq^2) - sq^2 \ge 0$ (accepting at indifference). A rejected request gives the buyer $0$. Hence, given a belief function $\hat\theta(\cdot)$ from requests to types, a type-$t$ buyer requesting $q$ earns $\mu(q,\theta_t,\hat\theta(q))$ if the seller accepts and $0$ otherwise.
--
--   **Separating equilibrium.** A request strategy $q(\cdot)$ on the two types and a belief function $\hat\theta(\cdot)$ form a pure-strategy separating perfect Bayesian equilibrium when
--   1. both requests are nonnegative;
--   2. the two types request different qualities, $q(\theta_H)\ne q(\theta_L)$;
--   3. beliefs are consistent on the equilibrium path: $\hat\theta(q(\theta_H)) = \theta_H$ and $\hat\theta(q(\theta_L)) = \theta_L$;
--   4. no type gains by deviating to any other request $q \ge 0$.
--
--   Beliefs off the equilibrium path are unrestricted.
--
--   **First-best requests and thresholds.** The first-best request under symmetric information is $q^*(\theta)=\min\{\gamma\theta/(s+\gamma k),\ \theta/(2k)\}$, and the cheap-signaling profile is $q^O_H = q^*(\theta_H)$, $q^O_L = q^*(\theta_L)$. The thresholds of Proposition 3 are
--   $$\Lambda_{H1}=\frac{\gamma(s+k)}{(1-\gamma)s},\quad \Lambda_{H2}=\frac{1+\gamma}{1-\gamma},\quad \Lambda_L=\frac{s}{\gamma k},\quad \Lambda=\max\{\min\{\Lambda_{H1},\Lambda_{H2}\},\Lambda_L\}.$$
--   The incentive constraints (11)–(12) are $\mathrm{IC}'_H:\ \mu(q^*(\theta_H),\theta_H,\theta_H)\ge\mu(q^*(\theta_L),\theta_H,\theta_L)$ and $\mathrm{IC}'_L:\ \mu(q^*(\theta_L),\theta_L,\theta_L)\ge\mu(q^*(\theta_H),\theta_L,\theta_H)$. The two belief functions of Proposition 3 are: $\hat\theta(q^O_H)=\theta_H$ and $\hat\theta(q)=\theta_L$ for every other $q$; and $\hat\theta(q^O_L)=\theta_L$ and $\hat\theta(q)=\theta_H$ for every other $q$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The price stage is in reduced form: it enters only through $\mu$ and through the seller's acceptance inequality, as in the paper; it is not modeled as a game. The seller's stage-2 rationality is built into the acceptance rule (accept iff its expected payoff under its belief is $\ge 0$), with acceptance at a tie as printed. A belief function is a total map from $\mathbb R$ to the two types. Deviations range over $q\ge 0$. Both $\max\{\cdot,0\}$ terms of (9) are kept literally. The parameter $\alpha$ does not enter this mission but is kept in the standing assumptions as printed.
-- source:
--   Guo, The Voice of Customers in Customization, SSRN working paper 3994319 (version of 2023-11-29, https://ssrn.com/abstract=3994319), pp. 5–9 §2, (1); pp. 16–17 §3.3, (9)–(12), Proposition 3

import Mathlib
import Definitions.Def_CustomerVoice_ALearn_Setting

namespace CustomerVoice.OLearn

/-- Model primitives (§2): preferences `θH`, `θL`, prior share `α` of high types,
seller's bargaining probability `γ`, production cost `k`, selling cost `s`. -/
structure Model where
  θH : ℝ
  θL : ℝ
  α : ℝ
  γ : ℝ
  k : ℝ
  s : ℝ

/-- The quality preference of a buyer type. -/
def Model.θ (M : Model) : CustomerVoice.ALearn.BType → ℝ
  | .H => M.θH
  | .L => M.θL

/-- Standing assumptions of §2: `θH > θL > 0`, `α, γ ∈ (0, 1)`, `k > 0`, `s > 0`. -/
def Model.Standing (M : Model) : Prop :=
  0 < M.θL ∧ M.θL < M.θH ∧
  0 < M.α ∧ M.α < 1 ∧
  0 < M.γ ∧ M.γ < 1 ∧
  0 < M.k ∧ 0 < M.s

/-- (9): `µ(q, θ, θ̂) = γ max{θq − θ̂q, 0} + (1 − γ) max{θq − kq², 0}`, the expected payoff,
conditional on acceptance, of a buyer with true preference `θ` believed to be `θ̂`
who requested quality `q`. -/
noncomputable def Model.mu (M : Model) (q θ θh : ℝ) : ℝ :=
  M.γ * max (θ * q - θh * q) 0 +
    (1 - M.γ) * max (θ * q - M.k * q ^ 2) 0

/-- Seller acceptance as printed (§3.3, p. 16): the seller accepts request `q` from a buyer
believed to be `θ̂` iff `γ(θ̂q − kq²) − sq² ≥ 0` (accepting at indifference). -/
def Model.accepts (M : Model) (θh q : ℝ) : Prop :=
  0 ≤ M.γ * (θh * q - M.k * q ^ 2) - M.s * q ^ 2

/-- A type-`t` buyer's payoff from requesting `q` when the seller's belief function is `bel`:
`µ(q, θ_t, θ̂(q))` if the seller accepts, `0` if it rejects. -/
noncomputable def Model.pay (M : Model) (bel : ℝ → CustomerVoice.ALearn.BType) (t : CustomerVoice.ALearn.BType)
    (q : ℝ) : ℝ := by
  classical
  exact if M.accepts (M.θ (bel q)) q then M.mu q (M.θ t) (M.θ (bel q)) else 0

/-- A pure-strategy separating perfect Bayesian equilibrium of the O-Learning game with request
strategy `req` and seller belief function `bel`: requests are nonnegative and distinct, beliefs
are consistent on path, and no type gains by deviating to any request `q ≥ 0`. -/
def Model.OSepEq (M : Model) (req : CustomerVoice.ALearn.BType → ℝ) (bel : ℝ → CustomerVoice.ALearn.BType) : Prop :=
  (∀ t : CustomerVoice.ALearn.BType, 0 ≤ req t) ∧
  req .H ≠ req .L ∧
  (∀ t : CustomerVoice.ALearn.BType, bel (req t) = t) ∧
  (∀ t : CustomerVoice.ALearn.BType, ∀ q : ℝ, 0 ≤ q → M.pay bel t q ≤ M.pay bel t (req t))

/-- The first-best request under symmetric information (p. 16):
`q*(θ) = min{γθ/(s+γk), θ/(2k)}`. -/
noncomputable def Model.qStar (M : Model) (θ : ℝ) : ℝ :=
  min (M.γ * θ / (M.s + M.γ * M.k)) (θ / (2 * M.k))

/-- The cheap-signaling request profile `q^O_t = q*(θ_t)`. -/
noncomputable def Model.qO (M : Model) (t : CustomerVoice.ALearn.BType) : ℝ :=
  M.qStar (M.θ t)

/-- `ΛH1 = γ(s+k)/((1−γ)s)` (Proposition 3). -/
noncomputable def Model.LambdaH1 (M : Model) : ℝ :=
  M.γ * (M.s + M.k) / ((1 - M.γ) * M.s)

/-- `ΛH2 = (1+γ)/(1−γ)` (Proposition 3). -/
noncomputable def Model.LambdaH2 (M : Model) : ℝ :=
  (1 + M.γ) / (1 - M.γ)

/-- `ΛL = s/(γk)` (Proposition 3). -/
noncomputable def Model.LambdaL (M : Model) : ℝ :=
  M.s / (M.γ * M.k)

/-- `Λ = max{min{ΛH1, ΛH2}, ΛL}` (Proposition 3). -/
noncomputable def Model.Lambda (M : Model) : ℝ :=
  max (min M.LambdaH1 M.LambdaH2) M.LambdaL

/-- (11) `IC′_H : µ(q*(θH), θH, θH) ≥ µ(q*(θL), θH, θL)`. -/
def Model.ICH' (M : Model) : Prop :=
  M.mu (M.qO .L) M.θH M.θL ≤ M.mu (M.qO .H) M.θH M.θH

/-- (12) `IC′_L : µ(q*(θL), θL, θL) ≥ µ(q*(θH), θL, θH)`. -/
def Model.ICL' (M : Model) : Prop :=
  M.mu (M.qO .H) M.θL M.θH ≤ M.mu (M.qO .L) M.θL M.θL

/-- Proposition 3's belief for `γ ≤ s/k`: `θ̂(q^O_H) = θH`, and `θ̂(q) = θL` for every other `q`. -/
noncomputable def Model.belLow (M : Model) (q : ℝ) : CustomerVoice.ALearn.BType := by
  classical
  exact if q = M.qO .H then .H else .L

/-- Proposition 3's belief for `γ ≥ s/k`: `θ̂(q^O_L) = θL`, and `θ̂(q) = θH` for every other `q`. -/
noncomputable def Model.belHigh (M : Model) (q : ℝ) : CustomerVoice.ALearn.BType := by
  classical
  exact if q = M.qO .L then .L else .H

end CustomerVoice.OLearn


