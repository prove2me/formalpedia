-- Prove2me | Definitions.Def_PricingStars_Model
-- name    : PricingStars_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:29:34.49425+00:00
-- url     : https://prove2.me/theorems/8c49032a-b4be-454c-b311-1fa172659271
-- title:
--   Pricing for the Stars model: inference, demand, reviews, rating path, optimal plans and long-run outcome
-- statement:
--   A long-lived monopolist sells a good of true quality $\theta\in\mathbb R$ and discounts profits at rate $\delta\in(0,1)$. Each period a new unit mass of consumers with tastes $\omega\sim U[0,1]$ arrives; gross utility is $u(\mu,\omega)=\mu+\omega$ (1). A purchaser at price $p$ leaves the review $\psi(\mu,\omega,p)=\mu+\omega-\kappa p$ (2), where $\kappa\in[0,1)$ is the degree of price internalization. The average taste of purchasers above a cutoff $\omega^*$ is $\omega_e(\omega^*)=(1+\omega^*)/2$.
--
--   **Admissible sensitivities.** The rating sensitivity $\sigma$ ranges over
--   $$
--   S(\kappa)=\{\sigma\in(0,1]:\ (\kappa>1/2\Rightarrow \sigma<1-\kappa),\ (\kappa,\sigma)\neq(1/2,1)\}.
--   $$
--
--   **Inference and demand.** At aggregate rating $\bar\psi$ and price $p$, a pair $(\mu,\omega)$ is a consumer *inference* (Assumption 1) when
--   $$
--   \psi(\mu,\omega_e(\omega),p)=\bar\psi\quad\text{(CONS)},\qquad u(\mu,\omega)=p\quad\text{(RAT)}.
--   $$
--   The cutoff is $\tilde\omega(\bar\psi,p)=1-2(\bar\psi-p(1-\kappa))$ (6) and demand is $q(\bar\psi,p)=1-\tilde\omega(\bar\psi,p)$ (7).
--
--   **Reviews and ratings.** The induced average review is $\psi(\theta,\omega_e(\tilde\omega),p)=\theta+\omega_e(\tilde\omega(\bar\psi,p))-\kappa p$ (8), and the rating updates by
--   $$
--   \bar\psi_{t+1}=(1-\sigma)\bar\psi_t+\sigma\,\psi(\theta,\omega_e(\tilde\omega(\bar\psi_t,p_t)),p_t)\qquad(3),(19),
--   $$
--   from a given $\bar\psi_0$ (20), for a price plan $p_0,p_1,\dots$.
--
--   **Seller's problem.** The flow profit is $p\,q(\bar\psi,p)$. A plan is *optimal* from $\bar\psi_0$ for (18) when its discounted profit series $\sum_{t\ge0}\delta^t p_t q(\bar\psi_t,p_t)$ converges to some $V$, and for every price plan and every $\varepsilon>0$ the partial sums $\sum_{t<N}\delta^t p'_t q(\bar\psi'_t,p'_t)$ are at most $V+\varepsilon$ for all large $N$.
--
--   **Long run.** $(\Psi,p)$ is the *long-run outcome* when an optimal plan exists from every initial rating and along every optimal plan from every initial rating the ratings converge to $\Psi$ and the prices to $p$. At long-run rating $\Psi$ and price $p$, the long-run profit is $\tilde\pi=p\,q(\Psi,p)$ (31) and the long-run consumer surplus is
--   $$
--   \widetilde{CS}=\int_{\tilde\omega(\Psi,p)}^{1}(\theta+\omega-p)\,d\omega .
--   $$
--
--   These objects are the primitives on which the mission's comparative statics (Corollary 1) and its milestones are stated; the long-run rating and price are defined from the seller's problem, never from the closed forms (28)–(29).
--
--   **Formalization Note** The model is the paper's unclamped linear-quadratic one: demand may be negative or exceed one, cutoffs are not truncated to $[0,1]$ and prices are any reals. Periods start at $t=0$; the left side of the printed (19) is read as $\bar\psi_{t+1}$. The paper does not define $\widetilde{CS}$; the purchasers' surplus integral used here reproduces the paper's (71) with $\beta=1$. The quality prior $F$ and its support play no role and are not modelled.
-- source:
--   Stenzel–Wolf–Schmidt, Pricing for the Stars: Dynamic Pricing in the Presence of Rating Systems, CRC TR 224 DP No. 143 (Jan 2020), §2 (1)–(4), pp.5–6; Technical Assumptions and Assumption 1, p.7; §2.1 (6)–(8), pp.9–10; §3 (18)–(22), pp.12–13; (31) and Corollary 1, p.14 (PDF 7–17)

import Mathlib

open Filter Topology

namespace PricingStars

/-- The **admissible set** of rating sensitivities `σ` for price internalization `κ`
(Stenzel–Wolf–Schmidt, Pricing for the Stars, CRC TR 224 DP No. 143 (Jan 2020), §2 "Time"/"Reviews
and Rating System" (3)–(4), p.6 (PDF 8), and "Technical Assumptions", p.7 (PDF 9)):
`S(κ) = {σ ∈ (0,1] : (κ > 1/2 → σ < 1 − κ) ∧ (κ, σ) ≠ (1/2, 1)}`.

**Formalization Note** The paper takes `σ ∈ [σ̄, 1]` for an arbitrary `σ̄ > 0`; here every
`σ ∈ (0,1]` is allowed. The technical assumption "σ < 1 − κ whenever κ > 1/2" is kept. The single
point `(κ, σ) = (1/2, 1)` is removed: there the rating ignores the price and oscillates
(`ψ̄' = θ + 1 − ψ̄`), so the long-run limits of Proposition 1 do not exist. -/
def admissibleSet (κ : ℝ) : Set ℝ :=
  {σ | 0 < σ ∧ σ ≤ 1 ∧ (1 / 2 < κ → σ < 1 - κ) ∧ ¬(κ = 1 / 2 ∧ σ = 1)}

/-- Gross utility `u(μ, ω) = μ + ω` of a consumer with taste `ω` for a good of (believed) quality
`μ` (DP No. 143, (1), p.5 (PDF 7)). -/
def utility (μ ω : ℝ) : ℝ := μ + ω

/-- Review `ψ(μ, ω, p) = μ + ω − κp` left by a purchaser with taste `ω` at price `p` for quality
`μ` (DP No. 143, (2), p.6 (PDF 8)). -/
def review (κ μ ω p : ℝ) : ℝ := μ + ω - κ * p

/-- Average taste of purchasers above the cutoff `ω*`: `ω_e(ω*) = E[ω | ω ≥ ω*] = (1 + ω*)/2`
for `ω ~ U[0,1]` (DP No. 143, p.6 (PDF 8)).

**Formalization Note** The paper's linear-quadratic model uses this formula for every real cutoff
(it never truncates the cutoff to `[0,1]`), so it is defined on all of `ℝ`. -/
noncomputable def avgTaste (ω : ℝ) : ℝ := (1 + ω) / 2

/-- Assumption 1 (DP No. 143, p.7 (PDF 9)): `(μ, ω)` is a consumer **inference** at aggregate
rating `ψ̄` and price `p` when (CONS) `ψ(μ, ω_e(ω), p) = ψ̄` and (RAT) `u(μ, ω) = p`. -/
def IsInference (κ ψ p μ ω : ℝ) : Prop :=
  review κ μ (avgTaste ω) p = ψ ∧ utility μ ω = p

/-- Inferred cutoff taste `ω̃(ψ̄, p) = 1 − 2(ψ̄ − p(1 − κ))` (DP No. 143, (6), p.9 (PDF 11)).
The milestone `explicit_inference` proves that it is the cutoff of the unique inference. -/
def cutoff (κ ψ p : ℝ) : ℝ := 1 - 2 * (ψ - p * (1 - κ))

/-- Demand `q(ψ̄, p) = 1 − ω̃(ψ̄, p)` (DP No. 143, (7), p.9 (PDF 11)).

**Formalization Note** No clamping to `[0,1]`: as in the paper's linear-quadratic model, demand
may be negative or exceed one, and prices are arbitrary reals. -/
def demand (κ ψ p : ℝ) : ℝ := 1 - cutoff κ ψ p

/-- Induced average review at true quality `θ`, aggregate rating `ψ̄` and price `p`:
`ψ(θ, ω_e(ω̃(ψ̄, p)), p) = θ + ω_e(ω̃) − κp` (DP No. 143, (8), p.10 (PDF 12)). -/
noncomputable def inducedReview (θ κ ψ p : ℝ) : ℝ := review κ θ (avgTaste (cutoff κ ψ p)) p

/-- Rating update `ψ̄_{t+1} = (1 − σ)ψ̄_t + σψ_t` (DP No. 143, (3), p.6 (PDF 8); (19), (22),
pp.12–13), with `ψ_t` the induced average review (8). -/
noncomputable def nextRating (θ κ σ ψ p : ℝ) : ℝ := (1 - σ) * ψ + σ * inducedReview θ κ ψ p

/-- The rating path of a price plan `p₀, p₁, …` from the initial rating `ψ̄₀`
(DP No. 143, (19)–(20), p.12 (PDF 14)): `ψ̄_0 = ψ̄₀`, `ψ̄_{t+1} = (1 − σ)ψ̄_t + σψ(p_t, ψ̄_t)`.

**Formalization Note** Periods are indexed from `t = 0` as in (18)–(20); the left side of the
printed (19) is read as `ψ̄_{t+1}`. Appendix A's `ψ̄₁` is the same initial rating. -/
noncomputable def ratingPath (θ κ σ ψ₀ : ℝ) (plan : ℕ → ℝ) : ℕ → ℝ
  | 0 => ψ₀
  | t + 1 => nextRating θ κ σ (ratingPath θ κ σ ψ₀ plan t) (plan t)

/-- Flow profit `p · q(ψ̄, p)` (marginal cost `0`; DP No. 143, (18), p.12 (PDF 14)). -/
def flowProfit (κ ψ p : ℝ) : ℝ := p * demand κ ψ p

/-- The discounted flow profit `δ^t p_t q(p_t, ψ̄_t)` of period `t` along a plan
(the summand of (18), DP No. 143, p.12 (PDF 14)). -/
noncomputable def discProfit (θ δ κ σ ψ₀ : ℝ) (plan : ℕ → ℝ) (t : ℕ) : ℝ :=
  δ ^ t * flowProfit κ (ratingPath θ κ σ ψ₀ plan t) (plan t)

/-- The partial sum `∑_{t<N} δ^t p_t q(p_t, ψ̄_t)` of the seller's objective (18). -/
noncomputable def partialProfit (θ δ κ σ ψ₀ : ℝ) (plan : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ t ∈ Finset.range N, discProfit θ δ κ σ ψ₀ plan t

/-- A price plan is **optimal** from the initial rating `ψ̄₀` for the seller's problem
`max_{(p_t)} ∑_{t≥0} δ^t p_t q(p_t, ψ̄_t)` s.t. (19)–(20) (DP No. 143, (18)–(20), p.12 (PDF 14)):
its discounted profit series converges to some `V`, and every real price plan has partial sums
eventually at most `V + ε`, for every `ε > 0` (i.e. `limsup_N` of its partial sums is `≤ V`).

**Formalization Note** Competitors range over all real sequences, including those whose series
does not converge; comparing partial sums (not `tsum`, which is `0` for a non-summable series)
makes such plans count. -/
def IsOptimalPlan (θ δ κ σ ψ₀ : ℝ) (plan : ℕ → ℝ) : Prop :=
  ∃ V : ℝ, HasSum (discProfit θ δ κ σ ψ₀ plan) V ∧
    ∀ plan' : ℕ → ℝ, ∀ ε > 0, ∀ᶠ N in atTop, partialProfit θ δ κ σ ψ₀ plan' N ≤ V + ε

/-- `(Ψ, p)` is the **long-run outcome** (long-run rating and long-run price) of the seller's
problem (DP No. 143, §3, pp.13–14 (PDF 15–16), "the stationary equilibrium that we converge to"):
from every initial rating an optimal plan exists, and along every optimal plan from every initial
rating the ratings converge to `Ψ` and the prices to `p`. -/
def IsLongRunOutcome (θ δ κ σ Ψ p : ℝ) : Prop :=
  (∀ ψ₀ : ℝ, ∃ plan : ℕ → ℝ, IsOptimalPlan θ δ κ σ ψ₀ plan) ∧
    ∀ (ψ₀ : ℝ) (plan : ℕ → ℝ), IsOptimalPlan θ δ κ σ ψ₀ plan →
      Tendsto (ratingPath θ κ σ ψ₀ plan) atTop (𝓝 Ψ) ∧ Tendsto plan atTop (𝓝 p)

/-- Long-run profit `π̃ = p̃ · q(Ψ̃, p̃)` at long-run rating `Ψ` and price `p`
(DP No. 143, (31), first line, p.14 (PDF 16)). -/
def longRunProfit (κ Ψ p : ℝ) : ℝ := flowProfit κ Ψ p

/-- Long-run consumer surplus at long-run rating `Ψ` and price `p` for true quality `θ`:
`C̃S = ∫_{ω̃(Ψ, p)}^{1} (θ + ω − p) dω`, the net utility (1) of the purchasers
(DP No. 143, p.14 (PDF 16), Corollary 1(b)).

**Formalization Note** The paper does not define `C̃S`; this is the purchasers' true surplus at
the long-run rating and price, which reproduces the paper's (71) with `β = 1`. The integral is an
oriented interval integral of a continuous function. -/
noncomputable def longRunCS (θ κ Ψ p : ℝ) : ℝ :=
  ∫ ω in (cutoff κ Ψ p)..1, (θ + ω - p)

end PricingStars


