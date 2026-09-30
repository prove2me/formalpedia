-- Prove2me | Definitions.Def_MixFlex_Reliable_Model
-- name    : MixFlex_Reliable_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:59:13.412729+00:00
-- url     : https://prove2.me/theorems/e860f2c8-a005-48e5-bc29-deea36477efd
-- title:
--   The SD and SF networks of §2–§3 with perfectly reliable resources: terminal wealths (A-4)–(A-5), expected-utility, loss-averse (6) and CVaR (7)–(8) objectives, weak preference and the premium's sign
-- statement:
--   This file sets up the single-source newsvendor networks of Tomlin and Wang (2005), §2–§3, under the standing assumptions 1–3 of §3 and with every resource perfectly reliable ($\theta_1=\dots=\theta_{N+1}=1$), the setting of §3.3.
--
--   **Parameters.** There are $N$ products with a common contribution margin $p>0$ (§3 assumes $p_1=\dots=p_N$). The dedicated network SD has resources $n=1,\dots,N$, resource $n$ dedicated to product $n$, each with marginal total cost $c>0$; the flexible network SF has a single resource, labelled $N+1$, that can make every product, with marginal total cost $c_{N+1}$ (left free). The firm has initial wealth $w_0\in\mathbb R$. The loss-aversion coefficient satisfies $\beta\ge 1$ and the CVaR percentile satisfies $0<\eta\le 1$.
--
--   **Randomness.** On a probability space $(\Omega,\mathcal F,\mathbb P)$ the demand vector $\tilde X=(\tilde X_1,\dots,\tilde X_N)$ is measurable and each $\tilde X_n\ge 0$ almost surely. Nothing else is assumed about its joint distribution.
--
--   **Terminal wealths.** With all yields equal to one, a dedicated investment $K=(K_1,\dots,K_N)$ and a flexible investment $K_{N+1}$ give the terminal wealths
--   $$
--   w^{SD}(K)=w_0+p\sum_{n=1}^N\min\{\tilde X_n,K_n\}-c\sum_{n=1}^N K_n,\qquad
--   w^{SF}(K_{N+1})=w_0+p\min\Big\{\sum_{n=1}^N\tilde X_n,K_{N+1}\Big\}-c_{N+1}K_{N+1}.
--   $$
--
--   **Objectives.** For a terminal wealth $W$ with profit $\tilde W=W-w_0$:
--   1. the expected utility $E[u(W)]$ for a utility $u:\mathbb R\to\mathbb R$;
--   2. the loss-averse objective (6), $V_{LA}=w_0+E[\tilde W^+-\beta\tilde W^-]$ with $\tilde W^{+}=\max\{\tilde W,0\}$, $\tilde W^-=\max\{-\tilde W,0\}$, and the piecewise-linear utility $u_{LA}(w)=w_0+(w-w_0)^+-\beta(w-w_0)^-$;
--   3. the bracket of the CVaR objective (7)–(8), $w_0+v+\tfrac1\eta E[\min\{\tilde W-v,0\}]$, whose maximum over $v\in\mathbb R$ is $V_{CVaR_\eta}$.
--
--   **Preference and the flexibility premium.** SF is (weakly) preferred at flexible cost $c_{N+1}$ for a given objective when every nonnegative SD investment is matched or beaten by some nonnegative SF investment (for CVaR, every pair $(K,v)$ by some pair $(K_{N+1},v')$, since (8) maximizes over both jointly). The flexibility premium $\Delta$ of Definitions 1–2 is used only through its sign: "$\Delta\ge 0$" means SF is preferred for every $c_{N+1}\le c$ (p. 41: "the firm prefers the SF network as long as $c_{N+1}\le(1+\Delta)c$").
--
--   These objects are shared by every statement of the mission on Proposition 4.
--
--   **Formalization Note** The wealths are written in the closed form (A-4)–(A-5) of the paper's proof, i.e. the second-stage program (1)–(4) solved for the SD and SF technologies with unit yields; the reliability parameter and the committed-cost fraction $\lambda$ therefore do not appear ($c_j(1)=c_j$). $p>0$, $c>0$ and nonnegative, measurable demand are stated explicitly; $\beta\ge1$ and $\eta\in(0,1]$ are from p. 40. $\Delta$ and $c^I_{N+1}$ are not defined as numbers, since Definition 1's indifference cost need not exist or be unique, and optimal values are not taken as real suprema: preferences are the "for every SD investment there is an SF investment" statements above.
-- source:
--   Tomlin and Wang, On the value of mix flexibility and dual sourcing in unreliable newsvendor networks, Manufacturing Service Oper. Management 7(1), 2005, pp. 39–41, §2 (1)–(8), §3 assumptions 1–3, DEFINITION 1, DEFINITION 2; p. 45, §3.3 (the set U_1); pp. 52–53, Appendix A, proof of PROPOSITION 4, (A-4)–(A-5)

import Mathlib

namespace MixFlex.Reliable

open MeasureTheory

/-- The scalar parameters of §2–§3 (Tomlin–Wang 2005, pp. 40–41) under assumptions 1–3 with
perfectly reliable resources: the common contribution margin `p` (`p_1 = ⋯ = p_N`), the common
dedicated marginal total cost `c`, the initial wealth `w0`, the loss-aversion coefficient `beta`
of (6) and the CVaR percentile `eta` of (7)–(8). The flexible resource's marginal total cost
`c_{N+1}` is not a field: statements quantify over it. -/
structure Params where
  p : ℝ
  c : ℝ
  w0 : ℝ
  beta : ℝ
  eta : ℝ

/-- Standing conditions: `p` is a margin and `c` a cost (both positive), `β ≥ 1` (p. 40), and
`η ∈ (0, 1]` (p. 40: `η ∈ (0, 1)`, with `η = 1` the risk-neutral case). -/
structure Params.Standing (P : Params) : Prop where
  p_pos : 0 < P.p
  c_pos : 0 < P.c
  one_le_beta : 1 ≤ P.beta
  eta_pos : 0 < P.eta
  eta_le_one : P.eta ≤ 1

/-- The random environment: `μ` is a probability measure, the demand vector `X` is measurable,
and every demand is almost surely nonnegative. No other assumption on the joint law. -/
structure Setting {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → Fin N → ℝ) : Prop where
  prob : IsProbabilityMeasure μ
  meas : Measurable X
  demand_nonneg : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ X ω n

/-- Terminal wealth of the dedicated network SD under investment `K` (all yields equal to 1),
(A-4): `w₀ + p ∑ₙ min{xₙ, Kₙ} − c ∑ₙ Kₙ`. -/
noncomputable def wealthSD (P : Params) {N : ℕ} {Ω : Type*} (X : Ω → Fin N → ℝ)
    (K : Fin N → ℝ) (ω : Ω) : ℝ :=
  P.w0 + P.p * ∑ n, min (X ω n) (K n) - P.c * ∑ n, K n

/-- Terminal wealth of the flexible network SF with flexible marginal cost `cF` and investment
`K`, (A-5): `w₀ + p min{∑ₙ xₙ, K} − c_F K`. -/
noncomputable def wealthSF (P : Params) {N : ℕ} {Ω : Type*} (X : Ω → Fin N → ℝ)
    (cF K : ℝ) (ω : Ω) : ℝ :=
  P.w0 + P.p * min (∑ n, X ω n) K - cF * K

/-- Expected utility `E[u(W)]` of a terminal-wealth random variable `W`. -/
noncomputable def expectedUtility {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (u : ℝ → ℝ) (W : Ω → ℝ) : ℝ :=
  ∫ ω, u (W ω) ∂μ

/-- The loss-averse objective (6) for terminal wealth `W` (profit `W̃ = W − w₀`):
`w₀ + E[W̃⁺ − β W̃⁻]`. -/
noncomputable def lossAverseValue (P : Params) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (W : Ω → ℝ) : ℝ :=
  P.w0 + ∫ ω, (max (W ω - P.w0) 0 - P.beta * max (-(W ω - P.w0)) 0) ∂μ

/-- The piecewise-linear loss-averse utility with breakpoint `w₀`:
`u(w) = w₀ + (w − w₀)⁺ − β (w − w₀)⁻`. -/
noncomputable def uLA (P : Params) (w : ℝ) : ℝ :=
  P.w0 + max (w - P.w0) 0 - P.beta * max (-(w - P.w0)) 0

/-- The bracket of (7)–(8) for terminal wealth `W` and threshold `v`:
`w₀ + v + (1/η) E[min{W̃ − v, 0}]`. `V_CVaR(K)` is its maximum over `v`. -/
noncomputable def cvarObjective (P : Params) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (W : Ω → ℝ) (v : ℝ) : ℝ :=
  P.w0 + v + (1 / P.eta) * ∫ ω, min (W ω - P.w0 - v) 0 ∂μ

/-- SF is (weakly) preferred to SD at flexible cost `cF` for the expected-utility objective with
utility `u`: every nonnegative SD investment is matched or beaten by a nonnegative SF one. -/
def SFPreferredEU (P : Params) {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → Fin N → ℝ) (u : ℝ → ℝ) (cF : ℝ) : Prop :=
  ∀ K : Fin N → ℝ, (∀ n, 0 ≤ K n) → ∃ K' : ℝ, 0 ≤ K' ∧
    expectedUtility μ u (wealthSD P X K) ≤ expectedUtility μ u (wealthSF P X cF K')

/-- SF is (weakly) preferred to SD at flexible cost `cF` for the loss-averse objective (6). -/
def SFPreferredLA (P : Params) {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → Fin N → ℝ) (cF : ℝ) : Prop :=
  ∀ K : Fin N → ℝ, (∀ n, 0 ≤ K n) → ∃ K' : ℝ, 0 ≤ K' ∧
    lossAverseValue P μ (wealthSD P X K) ≤ lossAverseValue P μ (wealthSF P X cF K')

/-- SF is (weakly) preferred to SD at flexible cost `cF` for the CVaR objective (8), a maximum
over the investment and `v` jointly. -/
def SFPreferredCVaR (P : Params) {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → Fin N → ℝ) (cF : ℝ) : Prop :=
  ∀ K : Fin N → ℝ, (∀ n, 0 ≤ K n) → ∀ v : ℝ, ∃ K' v' : ℝ, 0 ≤ K' ∧
    cvarObjective P μ (wealthSD P X K) v ≤ cvarObjective P μ (wealthSF P X cF K') v'

/-- "Δ ≥ 0" for a preference `pref` indexed by the flexible cost: SF is preferred for every
flexible cost `c_{N+1} ≤ c` (p. 41: "the firm prefers the SF network as long as
`c_{N+1} ≤ (1 + Δ)c`"). -/
def PremiumNonneg (P : Params) (pref : ℝ → Prop) : Prop :=
  ∀ cF : ℝ, cF ≤ P.c → pref cF

end MixFlex.Reliable


