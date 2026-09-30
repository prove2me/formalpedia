-- Prove2me | Definitions.Def_MixFlex_RiskNeutral_Model
-- name    : MixFlex_RiskNeutral_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:51:30.296458+00:00
-- url     : https://prove2.me/theorems/29fd92c9-5a7e-45f5-a8b1-820cd42ad047
-- title:
--   The SD and SF networks of §2–§3 with Bernoulli yields: random profits (20), risk-neutral objectives (5), weak preference, the premium's sign, expected shortfall and correlation
-- statement:
--   This file sets up the single-source newsvendor networks of Tomlin and Wang (2005), §2–§3, under the standing assumptions 1–3 of §3.
--
--   **Parameters.** There are $N$ products with a common contribution margin $p>0$ (§3 assumes $p_1=\dots=p_N$). The dedicated network SD has resources $n=1,\dots,N$, resource $n$ dedicated to product $n$; the flexible network SF has one resource, labelled $N+1$, that can make every product. All resources have the same reliability $\theta\in[0,1]$ and the same marginal committed cost $\lambda\in[0,1]$; the dedicated resources have marginal total cost $c>0$, the flexible one has marginal total cost $c_{N+1}$ (left free).
--
--   **Randomness.** On a probability space $(\Omega,\mathcal F,\mathbb P)$ the demand vector is $\tilde X=(\tilde X_1,\dots,\tilde X_N)$, with each $\tilde X_n\ge 0$ almost surely and integrable. Each resource $j\in\{1,\dots,N+1\}$ has a Bernoulli yield $\tilde Y_j\in\{0,1\}$ with $\mathbb P(\tilde Y_j=1)=\theta$; the yields are mutually independent and independent of demand. An investment of $K_j$ in resource $j$ delivers capacity $\tilde Y_jK_j$ and costs $(\lambda+(1-\lambda)\tilde Y_j)c_jK_j$: $\lambda c_j$ per unit ordered plus $(1-\lambda)c_j$ per unit delivered.
--
--   **Profits and objectives.** For $K=(K_1,\dots,K_N)\ge 0$ the realized SD profit is the sum over products of (20),
--   $$
--   W^{SD}(K)=\sum_{n=1}^N\Big(-(\lambda+(1-\lambda)\tilde Y_n)\,c\,K_n+p\min\{\tilde X_n,\tilde Y_nK_n\}\Big),
--   $$
--   and for $K_{N+1}\ge 0$ the realized SF profit, with total demand $\tilde X_{N+1}=\tilde X_1+\dots+\tilde X_N$, is
--   $$
--   W^{SF}(K_{N+1})=-(\lambda+(1-\lambda)\tilde Y_{N+1})\,c_{N+1}K_{N+1}+p\min\{\tilde X_{N+1},\tilde Y_{N+1}K_{N+1}\}.
--   $$
--   The risk-neutral objectives (5), with initial wealth $w_0=0$, are $V^{SD}_{RN}(K)=\mathbb E[W^{SD}(K)]$ and $V^{SF}_{RN}(K_{N+1})=\mathbb E[W^{SF}(K_{N+1})]$.
--
--   **Preference and the flexibility premium.** SF is (weakly) preferred at flexible cost $c_{N+1}$ when $V^{SF,*}\ge V^{SD,*}$; this is encoded as: every nonnegative SD investment is matched or beaten by some nonnegative SF investment. SD preferred is the reverse. The flexibility premium $\Delta$ of Definitions 1–2 is used only through its sign: "$\Delta\ge 0$" means SF is preferred for every $c_{N+1}\le c$ (the page: "the firm prefers the SF network as long as $c_{N+1}\le(1+\Delta)c$"), and "$\Delta=0$" means $c_{N+1}=c$ is an indifference cost, i.e. SF and SD are each weakly preferred to the other at $c_{N+1}=c$.
--
--   **Expected shortfall and correlation.** For a random variable $Z$ and $\alpha\in(0,1)$, the lower quantile is $x_{(\alpha)}=\inf\{x:\mathbb P(Z\le x)\ge\alpha\}$ and the $\alpha$-expected shortfall of Acerbi and Tasche (2002) is
--   $$
--   ES_\alpha(Z)=-\frac1\alpha\Big(\mathbb E\big[Z\,\mathbf 1\{Z\le x_{(\alpha)}\}\big]+x_{(\alpha)}\big(\alpha-\mathbb P(Z\le x_{(\alpha)})\big)\Big).
--   $$
--   The correlation coefficient is $\rho(U,V)=\operatorname{Cov}(U,V)/\sqrt{\operatorname{Var}U\cdot\operatorname{Var}V}$.
--
--   These objects are shared by every statement of the mission on Proposition 1.
--
--   **Formalization Note** No joint density of demand is assumed (Proposition 1 speaks of "any demand random vector"; with a density, part (iii) would be vacuous for $N\ge 2$). Nonnegativity and integrability of demand, $p>0$, $c>0$, $\lambda,\theta\in[0,1]$ are stated explicitly; yield–demand independence is the paper's assumption (Appendix E, p. 56). $\Delta$ and $c^I_{N+1}$ are not defined as numbers, since Definition 1's indifference cost need not exist or be unique; optimal values are not taken as real suprema. Dedicated resource $n$ is `Fin.castSucc n` and the flexible resource is `Fin.last N`. The expected-shortfall formula is Acerbi–Tasche's general one (the paper uses it for continuous $Z$, where the correction term vanishes).
-- source:
--   Tomlin and Wang, On the value of mix flexibility and dual sourcing in unreliable newsvendor networks, Manufacturing Service Oper. Management 7(1), 2005, pp. 39–43, §2 (1)–(5), §3 assumptions 1–3, DEFINITION 1, DEFINITION 2, (20); Appendix A, proof of PROPOSITION 1, p. 52 (ES_α per Acerbi and Tasche 2002); Appendix E, p. 56 (yield–demand independence)

import Mathlib

namespace MixFlex.RiskNeutral

open MeasureTheory ProbabilityTheory

/-- The scalar parameters of §3 (Tomlin–Wang 2005, p. 41) under assumptions 1–3: the common
contribution margin `p` (`p_1 = ⋯ = p_N`), the common dedicated marginal total cost `c`, the common
marginal committed cost `lam` (λ) and the common reliability `theta` (θ). The flexible resource's
marginal total cost `c_{N+1}` is not a field: statements quantify over it. -/
structure Params where
  p : ℝ
  c : ℝ
  lam : ℝ
  theta : ℝ

/-- Standing sign conditions: `p` is a contribution margin and `c` a cost (both positive),
`λ ∈ [0, 1]` is the committed fraction of the cost, `θ ∈ [0, 1]` is a probability. -/
structure Params.Standing (P : Params) : Prop where
  p_pos : 0 < P.p
  c_pos : 0 < P.c
  lam_nonneg : 0 ≤ P.lam
  lam_le_one : P.lam ≤ 1
  theta_nonneg : 0 ≤ P.theta
  theta_le_one : P.theta ≤ 1

/-- The random environment of §2–§3 on a probability space `(Ω, μ)`: the demand vector
`X : Ω → Fin N → ℝ` of the `N` products, and the yields `Y : Ω → Fin (N + 1) → ℝ` of the `N + 1`
resources (dedicated resource `n` is `Fin.castSucc n`, the flexible resource `N + 1` is
`Fin.last N`). Yields are Bernoulli(θ), mutually independent and independent of demand; demands
are nonnegative and integrable. No joint density is assumed. -/
structure Setting (P : Params) {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → Fin N → ℝ) (Y : Ω → Fin (N + 1) → ℝ) : Prop where
  prob : IsProbabilityMeasure μ
  meas_X : Measurable X
  meas_Y : Measurable Y
  demand_nonneg : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ X ω n
  demand_int : ∀ n, Integrable (fun ω => X ω n) μ
  yield_01 : ∀ j, ∀ᵐ ω ∂μ, Y ω j = 0 ∨ Y ω j = 1
  yield_prob : ∀ j, μ.real {ω | Y ω j = 1} = P.theta
  yield_indep : iIndepFun (fun j ω => Y ω j) μ
  yield_demand_indep : IndepFun X Y μ

/-- Realized SD profit: the sum over products of (20),
`w_n = −(λ + (1 − λ) y_n) c K_n + p min{x_n, y_n K_n}`. -/
noncomputable def sdProfit (P : Params) {N : ℕ} {Ω : Type*} (X : Ω → Fin N → ℝ)
    (Y : Ω → Fin (N + 1) → ℝ) (K : Fin N → ℝ) (ω : Ω) : ℝ :=
  ∑ n, (-(P.lam + (1 - P.lam) * Y ω n.castSucc) * P.c * K n
    + P.p * min (X ω n) (Y ω n.castSucc * K n))

/-- Realized SF profit `w(K) = −c(y)′K + r(K, x, y)` for the single flexible resource with
marginal total cost `cF = c_{N+1}` and investment `K = K_{N+1}`: sales are
`min{x_1 + ⋯ + x_N, y_{N+1} K_{N+1}}`. -/
noncomputable def sfProfit (P : Params) {N : ℕ} {Ω : Type*} (X : Ω → Fin N → ℝ)
    (Y : Ω → Fin (N + 1) → ℝ) (cF K : ℝ) (ω : Ω) : ℝ :=
  -(P.lam + (1 - P.lam) * Y ω (Fin.last N)) * cF * K
    + P.p * min (∑ n, X ω n) (Y ω (Fin.last N) * K)

/-- Risk-neutral SD objective (5) with `w_0 = 0`: `V^{SD}_{RN}(K) = E[W^{SD}(K)]`. -/
noncomputable def vSD (P : Params) {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → Fin N → ℝ) (Y : Ω → Fin (N + 1) → ℝ) (K : Fin N → ℝ) : ℝ :=
  ∫ ω, sdProfit P X Y K ω ∂μ

/-- Risk-neutral SF objective (5) with `w_0 = 0`: `V^{SF}_{RN}(K_{N+1}) = E[W^{SF}(K_{N+1})]`. -/
noncomputable def vSF (P : Params) {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → Fin N → ℝ) (Y : Ω → Fin (N + 1) → ℝ) (cF K : ℝ) : ℝ :=
  ∫ ω, sfProfit P X Y cF K ω ∂μ

/-- SF is (weakly) preferred at flexible cost `cF`, i.e. `V^{SF,*} ≥ V^{SD,*}`: every nonnegative
SD investment is matched or beaten by some nonnegative SF investment. -/
def SFPreferred (P : Params) {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → Fin N → ℝ) (Y : Ω → Fin (N + 1) → ℝ) (cF : ℝ) : Prop :=
  ∀ K : Fin N → ℝ, (∀ n, 0 ≤ K n) → ∃ K' : ℝ, 0 ≤ K' ∧ vSD P μ X Y K ≤ vSF P μ X Y cF K'

/-- SD is (weakly) preferred at flexible cost `cF`, i.e. `V^{SD,*} ≥ V^{SF,*}`. -/
def SDPreferred (P : Params) {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → Fin N → ℝ) (Y : Ω → Fin (N + 1) → ℝ) (cF : ℝ) : Prop :=
  ∀ K' : ℝ, 0 ≤ K' → ∃ K : Fin N → ℝ, (∀ n, 0 ≤ K n) ∧ vSF P μ X Y cF K' ≤ vSD P μ X Y K

/-- "The flexibility premium is nonnegative" (Definitions 1–2, p. 41): the firm prefers SF for
every flexible marginal total cost `c_{N+1} ≤ c = (1 + 0) c`. -/
def PremiumNonneg (P : Params) {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → Fin N → ℝ) (Y : Ω → Fin (N + 1) → ℝ) : Prop :=
  ∀ cF : ℝ, cF ≤ P.c → SFPreferred P μ X Y cF

/-- "The flexibility premium is zero" (Definitions 1–2, p. 41): `c_{N+1} = c` is an indifference
cost, i.e. `V^{SF,*} = V^{SD,*}` at `c_{N+1} = c`. -/
def PremiumZero (P : Params) {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → Fin N → ℝ) (Y : Ω → Fin (N + 1) → ℝ) : Prop :=
  SFPreferred P μ X Y P.c ∧ SDPreferred P μ X Y P.c

/-- The lower `α`-quantile `x_(α) = inf {x | α ≤ P(Z ≤ x)}` (Acerbi–Tasche 2002). Used only for
`α ∈ (0, 1)`, where the set is nonempty and bounded below. -/
noncomputable def lowerQuantile {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Z : Ω → ℝ)
    (α : ℝ) : ℝ :=
  sInf {x : ℝ | α ≤ μ.real {ω | Z ω ≤ x}}

/-- The `α`-expected shortfall of Acerbi–Tasche (2002):
`ES_α(Z) = −(1/α) (E[Z 1{Z ≤ q}] + q (α − P(Z ≤ q)))` with `q = x_(α)` the lower `α`-quantile. -/
noncomputable def expectedShortfall {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Z : Ω → ℝ)
    (α : ℝ) : ℝ :=
  -(1 / α) * ((∫ ω, Z ω * (if Z ω ≤ lowerQuantile μ Z α then 1 else 0) ∂μ)
    + lowerQuantile μ Z α * (α - μ.real {ω | Z ω ≤ lowerQuantile μ Z α}))

/-- The correlation coefficient `ρ(U, V) = Cov(U, V) / √(Var U · Var V)`. -/
noncomputable def correlation {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (U V : Ω → ℝ) : ℝ :=
  covariance U V μ / Real.sqrt (variance U μ * variance V μ)

end MixFlex.RiskNeutral


