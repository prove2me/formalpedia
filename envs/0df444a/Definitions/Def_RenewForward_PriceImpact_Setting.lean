-- Prove2me | Definitions.Def_RenewForward_PriceImpact_Setting
-- name    : RenewForward_PriceImpact_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:18:22.447208+00:00
-- url     : https://prove2.me/theorems/824b2b2e-c23a-4d3c-a6ef-39a039bd8a31
-- title:
--   §3–§4 — the forward-spot electricity market: demand θ, wind yield ξ, inverse demand (6), profits (1), (3), utility (9), spot Cournot game, retailer optimality, clearing, equilibrium
-- statement:
--   This file sets up the two-stage wholesale electricity market of Peura and Bunn (§3–§4).
--
--   **Parameters.** The intercept $a$ of the elastic industrial demand $D_I = a - p_s$, the conventional producers' marginal cost $c$, the fixed retail price $p_R$, the common risk-aversion coefficient $\lambda$, and the number $N_R \ge 1$ of retailers.
--
--   **Uncertainty.** On a probability space $(\Omega, \mathcal F, P)$ live the total retail demand $\theta$ and the wind yield $\xi$. The *standing assumptions* are:
--   1. $\theta$ and $\xi$ are measurable and independent;
--   2. $\theta$ takes values in a bounded interval $[\underline\theta, \bar\theta]$ and $\xi$ in $[0, 1]$;
--   3. $\lambda > 0$ and $N_R \ge 1$;
--   4. $V(\theta) > 0$ and $V(\xi) > 0$ (demand and wind output are genuinely uncertain in the forward market).
--
--   The moments are $\mu_\theta = E[\theta]$, $\sigma_\theta^2 = V(\theta)$, $\tau_\theta = E[(\theta - \mu_\theta)^3]$, and likewise $\mu_\xi, \sigma_\xi^2, \tau_\xi$; further $CV_\xi = \sigma_\xi/\mu_\xi$ and $\tau^N_\xi = \tau_\xi/\sigma_\xi^3$.
--
--   **Spot stage.** Wind capacity is $k_W$, so available wind output is $\xi k_W$. With forward positions $f_{P1}, f_{P2}$ fixed, the two conventional producers play Cournot on the inverse residual demand
--   $$p_s = a + \theta - \xi k_W - (q_{P1} + q_{P2}),$$
--   each maximizing its spot profit $p_s (q_{Pi} - f_{Pi}) - c\, q_{Pi}$ over $q_{Pi} \in \mathbb R$, at each realization of $(\theta, \xi)$. Write $q_0 = a - c + \theta - \xi k_W$ and $p_0 = a + 2c + \theta - \xi k_W$. The candidate spot outcome of Lemma 1 is
--   $$q^*_{Pi} = \frac{q_0 + 2 f_{Pi} - f_{Pj}}{3}, \qquad p_s = \frac{p_0 - (f_{Pi} + f_{Pj})}{3}.$$
--
--   **Forward stage.** Every participant maximizes the mean-variance utility
--   $$U(\pi) = E[\pi] - \frac{\lambda}{2} V(\pi).$$
--   A retailer with share $\theta/N_R$, forward position $f_{Ri}$ and forward price $p_f$ earns $p_R \theta/N_R - p_s(\theta/N_R - f_{Ri}) - p_f f_{Ri}$, where $p_s$ is the Lemma 1 spot price at the total forward sales $F$. It is a price taker: $f_{Ri}$ maximizes its utility with $p_f$ and $F$ held fixed. The market *clears* at $(p_f, F)$ if optimal retailer positions summing to $F$ exist. A producer $i$ with positions $(f_{Pi}, f_{Pj})$ earns $p_s(q^*_{Pi} - f_{Pi}) + p_f f_{Pi} - c\, q^*_{Pi}$. A triple $(f_{P1}, f_{P2}, p_f)$ is a *forward-spot equilibrium* if the market clears at $p_f$ with sales $f_{P1} + f_{P2}$ and neither producer can raise its utility by a deviation $f'$ evaluated at a forward price $p_f'$ that clears the market at the deviated sales.
--
--   The equilibrium is defined through these optimization problems only; the closed forms of Theorem 1 are not used in any definition.
--
--   **Formalization Note.** `lam` stands for $\lambda$ (a Lean keyword), `mu…`, `sig2…`, `tau…` for the moments, and `w : Ω` for a sample point. The spot inverse demand is (6) without its $\max\{\cdot, 0\}$, as licensed by Assumption 1, on all of $k_W$ and all realizations; quantities range over $\mathbb R$. The bounds on $\theta$, $\xi$ hold at every sample point; they make every profit bounded, so all variances are finite. $V(\theta) > 0$, $V(\xi) > 0$ are added from p. 7 ("both demand and effective supply capacity are uncertain"). The footnote conditions $N_R > 6$ and $c \le \min\{p_R, a\}$ are not assumed.
-- source:
--   Peura & Bunn, Renewable power and electricity prices: The impact of forward markets, author-accepted manuscript, LBS Research Online eprint 1432 (Management Science 67(8), 2021, doi:10.1287/mnsc.2020.3710), pp. 7–14, (1), (3), (6), (9), Assumption 1, Lemma 1, §4.2

import Mathlib

namespace RenewForward.PriceImpact

open MeasureTheory ProbabilityTheory

/-- The deterministic parameters of the market (§3–§4): the intercept `a` of the industrial demand
`D_I = a − p_s`, the conventional producers' marginal cost `c`, the fixed retail price `pR`, the common
risk-aversion coefficient `lam` (the paper's `λ`, a Lean keyword) and the number `NR` of retailers. -/
structure Params where
  a : ℝ
  c : ℝ
  pR : ℝ
  lam : ℝ
  NR : ℕ

section Moments

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The mean `E[X] = ∫ X dP`. -/
noncomputable def mean (P : Measure Ω) (X : Ω → ℝ) : ℝ := ∫ w, X w ∂P

/-- The third central moment ("third moment (unnormalized skewness)", p. 9), `E[(X − E[X])³]`. -/
noncomputable def thirdCentral (P : Measure Ω) (X : Ω → ℝ) : ℝ := ∫ w, (X w - mean P X) ^ 3 ∂P

/-- `µ_θ`. -/
noncomputable def muTheta (P : Measure Ω) (θ : Ω → ℝ) : ℝ := mean P θ
/-- `σ²_θ`. -/
noncomputable def sig2Theta (P : Measure Ω) (θ : Ω → ℝ) : ℝ := variance θ P
/-- `τ_θ` (central). -/
noncomputable def tauTheta (P : Measure Ω) (θ : Ω → ℝ) : ℝ := thirdCentral P θ
/-- `µ_ξ`. -/
noncomputable def muXi (P : Measure Ω) (ξ : Ω → ℝ) : ℝ := mean P ξ
/-- `σ²_ξ`. -/
noncomputable def sig2Xi (P : Measure Ω) (ξ : Ω → ℝ) : ℝ := variance ξ P
/-- `τ_ξ` (central). -/
noncomputable def tauXi (P : Measure Ω) (ξ : Ω → ℝ) : ℝ := thirdCentral P ξ

/-- Proposition 2's coefficient of variation `CV_ξ = σ_ξ / µ_ξ`. -/
noncomputable def cvXi (P : Measure Ω) (ξ : Ω → ℝ) : ℝ := Real.sqrt (sig2Xi P ξ) / muXi P ξ

/-- Proposition 2's normalized skewness `τ^N_ξ = τ_ξ / σ³_ξ`. -/
noncomputable def tauNXi (P : Measure Ω) (ξ : Ω → ℝ) : ℝ := tauXi P ξ / Real.sqrt (sig2Xi P ξ) ^ 3

/-- The standing assumptions of §3–§4 (p. 7, §3.2 p. 9, §4.2 p. 13): `θ` and `ξ` are measurable and
independent, `θ` has bounded support `[θ̲, θ̄]`, the yield `ξ` takes values in `[0, 1]` (pointwise, at every
sample point), `λ > 0`, there is at least one retailer, and both demand and wind yield are genuinely
uncertain (`0 < V(θ)`, `0 < V(ξ)`). -/
def Standing (M : Params) (P : Measure Ω) (θ ξ : Ω → ℝ) : Prop :=
  Measurable θ ∧ Measurable ξ ∧ IndepFun θ ξ P ∧
  (∃ lo hi : ℝ, ∀ w, θ w ∈ Set.Icc lo hi) ∧ (∀ w, ξ w ∈ Set.Icc (0 : ℝ) 1) ∧
  0 < M.lam ∧ 1 ≤ M.NR ∧ 0 < variance θ P ∧ 0 < variance ξ P

end Moments

section Spot

variable {Ω : Type*}

/-- `q0 := a − c + θ − ξ k_W` (Lemma 1), production without forward contracts. -/
def q0 (M : Params) (θ ξ : Ω → ℝ) (kW : ℝ) (w : Ω) : ℝ := M.a - M.c + θ w - ξ w * kW

/-- `p0 := a + 2c + θ − ξ k_W` (Lemma 1), the spot price without forward contracts. -/
def p0 (M : Params) (θ ξ : Ω → ℝ) (kW : ℝ) (w : Ω) : ℝ := M.a + 2 * M.c + θ w - ξ w * kW

/-- The inverse residual spot demand (6), interior branch (Assumption 1):
`p_s = a + θ − ξ k_W − (q_i + q_j)`. -/
def spotPrice' (M : Params) (θ ξ : Ω → ℝ) (kW qi qj : ℝ) (w : Ω) : ℝ :=
  M.a + θ w - ξ w * kW - (qi + qj)

/-- A conventional producer's spot-stage profit, (1) without the forward revenue `p_f f_Pi` (sunk at the
spot stage): `p_s (q_i − f_i) − c q_i`. -/
def spotProfit (M : Params) (θ ξ : Ω → ℝ) (kW fi qi qj : ℝ) (w : Ω) : ℝ :=
  spotPrice' M θ ξ kW qi qj w * (qi - fi) - M.c * qi

/-- `(q1, q2)` is a (Cournot–Nash) spot equilibrium at the realization `w` given forward positions
`(f1, f2)`: each quantity maximizes its producer's spot profit over all reals given the other. -/
def IsSpotEq (M : Params) (θ ξ : Ω → ℝ) (kW f1 f2 : ℝ) (w : Ω) (q1 q2 : ℝ) : Prop :=
  (∀ q : ℝ, spotProfit M θ ξ kW f1 q q2 w ≤ spotProfit M θ ξ kW f1 q1 q2 w) ∧
  (∀ q : ℝ, spotProfit M θ ξ kW f2 q q1 w ≤ spotProfit M θ ξ kW f2 q2 q1 w)

/-- The spot equilibrium quantity of Lemma 1, (7): `(q0 + 2 f_i − f_j)/3`. Lemma 1 (a milestone) proves it is
the unique spot equilibrium; the forward stage uses it as the anticipated spot outcome. -/
noncomputable def spotQ (M : Params) (θ ξ : Ω → ℝ) (kW fi fj : ℝ) (w : Ω) : ℝ :=
  (q0 M θ ξ kW w + 2 * fi - fj) / 3

/-- The spot equilibrium price of Lemma 1, (8), at total forward sales `F = f_i + f_j`: `(p0 − F)/3`. -/
noncomputable def spotP (M : Params) (θ ξ : Ω → ℝ) (kW F : ℝ) (w : Ω) : ℝ := (p0 M θ ξ kW w - F) / 3

end Spot

section Forward

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The mean-variance utility (9): `U(π) = E[π] − (λ/2) V(π)`. -/
noncomputable def utility (M : Params) (P : Measure Ω) (X : Ω → ℝ) : ℝ :=
  (∫ w, X w ∂P) - M.lam / 2 * variance X P

/-- Retailer profit (3) with share `θ_Ri = θ/N_R`, own forward position `fr`, forward price `pf`, and the
spot price of Lemma 1 at total forward sales `F`: `p_R θ_Ri − p_s (θ_Ri − f_Ri) − p_f f_Ri`. -/
noncomputable def retailerProfit (M : Params) (θ ξ : Ω → ℝ) (kW F pf fr : ℝ) (w : Ω) : ℝ :=
  M.pR * (θ w / M.NR) - spotP M θ ξ kW F w * (θ w / M.NR - fr) - pf * fr

/-- A price-taking retailer's optimal position: `fr` maximizes `U` of its profit over all reals, with the
forward price `pf` and the total forward sales `F` (hence the law of `p_s`) taken as given. -/
def IsRetailerOpt (M : Params) (P : Measure Ω) (θ ξ : Ω → ℝ) (kW F pf fr : ℝ) : Prop :=
  ∀ f' : ℝ, utility M P (retailerProfit M θ ξ kW F pf f') ≤
    utility M P (retailerProfit M θ ξ kW F pf fr)

/-- The forward market clears at price `pf` with total producer sales `F`: there are optimal positions of
the `N_R` retailers summing to `F` (`f_P = f_R`, zero net supply). -/
def Clears (M : Params) (P : Measure Ω) (θ ξ : Ω → ℝ) (kW pf F : ℝ) : Prop :=
  ∃ fR : Fin M.NR → ℝ, (∀ i, IsRetailerOpt M P θ ξ kW F pf (fR i)) ∧ ∑ i, fR i = F

/-- Producer `i`'s profit (1) at forward positions `(fi, fj)`, forward price `pf`, and the Lemma 1 spot
outcome: `p_s (q_i − f_i) + p_f f_i − c q_i`. -/
noncomputable def producerProfit (M : Params) (θ ξ : Ω → ℝ) (kW fi fj pf : ℝ) (w : Ω) : ℝ :=
  spotP M θ ξ kW (fi + fj) w * (spotQ M θ ξ kW fi fj w - fi) + pf * fi - M.c * spotQ M θ ξ kW fi fj w

/-- A forward-spot equilibrium `(f1, f2, pf)`: the forward market clears at `pf` with sales `f1 + f2`, and no
producer gains by deviating to any `f'` when the deviation is evaluated at **its own** clearing price `pf'`
(producers have forward market power, p. 13). -/
def IsFwdEq (M : Params) (P : Measure Ω) (θ ξ : Ω → ℝ) (kW f1 f2 pf : ℝ) : Prop :=
  Clears M P θ ξ kW pf (f1 + f2) ∧
  (∀ f' pf' : ℝ, Clears M P θ ξ kW pf' (f' + f2) →
    utility M P (producerProfit M θ ξ kW f' f2 pf') ≤ utility M P (producerProfit M θ ξ kW f1 f2 pf)) ∧
  (∀ f' pf' : ℝ, Clears M P θ ξ kW pf' (f1 + f') →
    utility M P (producerProfit M θ ξ kW f' f1 pf') ≤ utility M P (producerProfit M θ ξ kW f2 f1 pf))

end Forward

end RenewForward.PriceImpact


