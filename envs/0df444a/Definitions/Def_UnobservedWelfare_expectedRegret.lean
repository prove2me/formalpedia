-- Prove2me | Definitions.Def_UnobservedWelfare_expectedRegret
-- name    : UnobservedWelfare_expectedRegret
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:35.503813+00:00
-- url     : https://prove2.me/theorems/acb7805c-9f76-41ad-8fdc-50479601dd77
-- title:
--   Policies, executions, inventory, welfare $\mathrm{ALG}_T$, benchmark $\mathrm{OPT}^{\mathrm{agg}}_T$ and expected regret
-- statement:
--   Rounds $t=1,\dots,T$; buyer types $\theta_1,\dots,\theta_T$ are i.i.d. with an unknown law $P$ on a measurable type space $\Theta$.
--
--   1. **Policy.** A (deterministic) policy maps the history $(p_j,X_j)_{j<t}$ of posted prices and purchases to the production and price $(q_t,p_t)$ of round $t$. It is **purchase-based** if it is measurable and always outputs $q_t\in[0,1]^m$ and $p_t\gg0$.
--   2. **Execution.** On a probability space $(\Omega,\mu)$ there are a seed $\sigma$-algebra $\mathcal F_0$ (randomness of the policy and of tie-breaking) and the types, i.i.d. with law $P$ and independent of $\mathcal F_0$; the filtration is $\mathcal F_t=\sigma(\mathcal F_0,\theta_1,\dots,\theta_t)$. Production and price of round $t$ are $\mathcal F_{t-1}$-measurable, $q_t\in[0,1]^m$, $p_t\gg0$, and the purchase $X_t$ is $\mathcal F_t$-measurable with $X_t\in D_{\theta_t}(p_t)$ on every path (every permitted demand selection).
--   3. **Inventory.** $I_0=0$, $A_t=I_{t-1}+q_t$, $I_t=A_t-X_t$; the execution is **safe** if $I_t\ge0$ for every $t\in[T]$ on every path.
--   4. **Welfare.**
--   $$\mathrm{ALG}_T=\sum_{t=1}^T u_{\theta_t}(X_t)-\sum_{t=1}^T c(q_t),\qquad \mathrm{OPT}^{\mathrm{agg}}_T=\sup_{\substack{x_t\ge0,\ \bar q_t\in[0,1]^m\\ \sum_t x_t\le\sum_t\bar q_t}}\Big\{\sum_{t=1}^T u_{\theta_t}(x_t)-\sum_{t=1}^T c(\bar q_t)\Big\}.$$
--   5. **Expected regret** $\mathrm{Reg}_T=\mathbb E[\mathrm{OPT}^{\mathrm{agg}}_T-\mathrm{ALG}_T]$.
--
--   **Formalization Note** Rounds are 0-based in Lean: round `k` is the paper's round $t=k+1$, and `invAfter n` is $I_n$. The policy type mentions no type space or distribution, so a policy cannot use them. The expectation is an outer integral: the infimum of $\int g\,d\mu$ over measurable $g\ge(\mathrm{OPT}^{\mathrm{agg}}_T-\mathrm{ALG}_T)_+$ almost surely; it is the ordinary expectation when the gap is measurable.
-- source:
--   Cheng–Tao–Xing, Maximizing Unobserved Welfare: Logarithmic Regret from Purchases, manuscript (STOC 2027 submission; held artifact sha256 cfd42fa2b0b4d51bad26ff5715acac275b66e830e1391d884542854ddde215fe), §2 "Policies" and "Welfare and Regret", pp.17–18 (PDF pp.19–20), (26), (31), (32); Appendix C.2, p.45 (PDF p.47)

import Mathlib
import Definitions.Def_UnobservedWelfare_IsRC

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace UnobservedWelfare

/-- A deterministic pricing and production policy for `m` goods (Cheng–Tao–Xing manuscript, §2
"Policies", p.17 (PDF p.19)): in (0-based) round `k` it maps the history of past posted prices and
purchases `(p_j, X_j)`, `j < k`, to the round's production and posted price `(q_k, p_k)`.

**Formalization Note** The type mentions neither the type space, the type distribution nor the
utilities, so a policy "uses only m, T, W, c and past prices and purchases" by construction (it is
chosen after `m, T, W, c`). The paper's purchase-based policies may also use their own random
choices; the goal asserts the existence of a deterministic one. Measurability and validity of
outputs are the separate predicate `IsPurchasePolicy`. -/
def Policy (m : ℕ) : Type :=
  (k : ℕ) → (Fin k → (Fin m → ℝ) × (Fin m → ℝ)) → (Fin m → ℝ) × (Fin m → ℝ)

/-- A purchase-based policy (Cheng–Tao–Xing manuscript, §2 "Policies", p.17 (PDF p.19)): in every
round it chooses `(q_k, p_k) ∈ [0,1]^m × ℝ^m_{++}`, measurably in the past transactions.

**Formalization Note** The outputs are required to be valid on every history, including histories
that cannot occur. -/
structure IsPurchasePolicy {m : ℕ} (π : Policy m) : Prop where
  measurable : ∀ k, Measurable (π k)
  prod_mem : ∀ k h, (π k h).1 ∈ cube m
  price_pos : ∀ k h, (π k h).2 ∈ posOrthant m

/-- One execution of the market of Cheng–Tao–Xing manuscript, §2, pp.15–17 (PDF pp.17–19), and
Appendix C.2, p.45 (PDF p.47), on a probability space `(Ω, μ)`, for horizon `T`.

* `θ k` is the type of the buyer of (0-based) round `k`, i.e. the paper's `θ_{k+1}`; `F0` is the
  σ-algebra of the seed `ω₀` (randomness of the policy and of tie-breaking among demands).
* `θ 0, …, θ (T-1)` are i.i.d. with law `P` and jointly independent of `F0`.
* `q k`, `p k`, `X k` are the production, posted price and purchase of round `k` (paper's
  `q_{k+1}, p_{k+1}, X_{k+1}`). Production and price are measurable with respect to the past
  `fil k`, the purchase with respect to `fil (k+1)`, and on every `ω` the purchase is a bundle of the
  current buyer's demand set at the posted price ("every permitted demand selection").

**Formalization Note** Rounds are 0-based: Lean round `k < T` is the paper's round `t = k + 1`.
The filtration `fil k` (paper's `F_k`) is `F0` joined with the σ-algebras of `θ 0, …, θ (k-1)`. -/
structure Execution (m T : ℕ) {Θ : Type*} [MeasurableSpace Θ] (P : Measure Θ)
    (u : Θ → (Fin m → ℝ) → EReal) {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) where
  θ : ℕ → Ω → Θ
  measurable_θ : ∀ k, Measurable (θ k)
  law : ∀ k < T, μ.map (θ k) = P
  iIndep : iIndepFun (fun k : Fin T => θ k) μ
  F0 : MeasurableSpace Ω
  F0_le : F0 ≤ mΩ
  indep_seed : Indep F0 (⨆ k : Fin T, MeasurableSpace.comap (θ k) inferInstance) μ
  q : ℕ → Ω → (Fin m → ℝ)
  p : ℕ → Ω → (Fin m → ℝ)
  X : ℕ → Ω → (Fin m → ℝ)
  measurable_q : ∀ k < T,
    Measurable[F0 ⊔ ⨆ (j : ℕ) (_ : j < k), MeasurableSpace.comap (θ j) inferInstance] (q k)
  measurable_p : ∀ k < T,
    Measurable[F0 ⊔ ⨆ (j : ℕ) (_ : j < k), MeasurableSpace.comap (θ j) inferInstance] (p k)
  measurable_X : ∀ k < T,
    Measurable[F0 ⊔ ⨆ (j : ℕ) (_ : j < k + 1), MeasurableSpace.comap (θ j) inferInstance] (X k)
  q_mem : ∀ k < T, ∀ ω, q k ω ∈ cube m
  p_pos : ∀ k < T, ∀ ω, p k ω ∈ posOrthant m
  X_mem : ∀ k < T, ∀ ω, X k ω ∈ demand (u (θ k ω)) (p k ω)

namespace Execution

variable {m T : ℕ} {Θ : Type*} [MeasurableSpace Θ] {P : Measure Θ}
  {u : Θ → (Fin m → ℝ) → EReal} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The filtration `F_k = σ(ω₀, θ_1, …, θ_k)` (Cheng–Tao–Xing manuscript, Appendix C.2, p.45
(PDF p.47)); with 0-based types this is `F0 ⊔ σ(θ 0, …, θ (k-1))`. -/
@[instance_reducible]
def fil (E : Execution m T P u μ) (k : ℕ) : MeasurableSpace Ω :=
  E.F0 ⊔ ⨆ (j : ℕ) (_ : j < k), MeasurableSpace.comap (E.θ j) inferInstance

/-- The remaining inventory `I_n = Σ_{t ≤ n} (q_t − X_t)` after the first `n` rounds, with
`I_0 = 0` (Cheng–Tao–Xing manuscript, (26), p.16 (PDF p.18)); the index `n` is the paper's. -/
def invAfter (E : Execution m T P u μ) (n : ℕ) (ω : Ω) : Fin m → ℝ :=
  ∑ j ∈ Finset.range n, (E.q j ω - E.X j ω)

/-- The available inventory `A_t = I_{t−1} + q_t` of paper round `t = k + 1` (Cheng–Tao–Xing
manuscript, (26), p.16 (PDF p.18)). -/
def avail (E : Execution m T P u μ) (k : ℕ) (ω : Ω) : Fin m → ℝ :=
  E.invAfter k ω + E.q k ω

/-- Safety (Cheng–Tao–Xing manuscript, §2 "Policies", p.17 (PDF p.19)): `I_t ≥ 0` for every
`t ∈ [T]` on every path. Delivery in full is built in, since `X` is the selected bundle. -/
def IsSafe (E : Execution m T P u μ) : Prop :=
  ∀ n, 1 ≤ n → n ≤ T → ∀ ω, 0 ≤ E.invAfter n ω

/-- The execution is driven by the deterministic policy `π`: in every round `k < T` and on every
path, `(q_k, p_k)` is `π` applied to the history `(p_j, X_j)_{j<k}`. -/
def DrivenBy (E : Execution m T P u μ) (π : Policy m) : Prop :=
  ∀ k < T, ∀ ω, (E.q k ω, E.p k ω) = π k (fun j : Fin k => (E.p j ω, E.X j ω))

/-- Realized online welfare `ALG_T = Σ_t u_{θ_t}(X_t) − Σ_t c(q_t)` (Cheng–Tao–Xing manuscript,
(31), p.18 (PDF p.20)). -/
noncomputable def ALG (E : Execution m T P u μ) (c : (Fin m → ℝ) → ℝ) (ω : Ω) : EReal :=
  (∑ k ∈ Finset.range T, u (E.θ k ω) (E.X k ω)) - ((∑ k ∈ Finset.range T, c (E.q k ω) : ℝ) : EReal)

/-- The aggregate offline benchmark (Cheng–Tao–Xing manuscript, (32), p.18 (PDF p.20)):
`OPT^agg_T = sup { Σ_t u_{θ_t}(x_t) − Σ_t c(q̄_t) : x_t ≥ 0, q̄_t ∈ [0,1]^m, Σ_t x_t ≤ Σ_t q̄_t }`. -/
noncomputable def OPTagg (E : Execution m T P u μ) (c : (Fin m → ℝ) → ℝ) (ω : Ω) : EReal :=
  ⨆ (x : Fin T → Fin m → ℝ) (qb : Fin T → Fin m → ℝ)
    (_ : (∀ k, 0 ≤ x k) ∧ (∀ k, qb k ∈ cube m) ∧ ∑ k, x k ≤ ∑ k, qb k),
    (∑ k : Fin T, u (E.θ k ω) (x k)) - ((∑ k : Fin T, c (qb k) : ℝ) : EReal)

/-- Expected welfare regret `Reg_T = E[OPT^agg_T − ALG_T]` (Cheng–Tao–Xing manuscript, p.18 (PDF
p.20)).

**Formalization Note** The gap is mapped to `[0, ∞]` (`EReal.toENNReal`, negative values to `0`;
the gap is nonnegative on every path of a safe execution) and its expectation is the outer
integral: the infimum of `∫⁻ g` over measurable `g` dominating the gap almost surely. It equals
the ordinary expectation whenever the gap is measurable, and needs no measurability of the
supremum `OPT^agg_T`. -/
noncomputable def expectedRegret (E : Execution m T P u μ) (c : (Fin m → ℝ) → ℝ) : ℝ≥0∞ :=
  ⨅ (g : Ω → ℝ≥0∞) (_ : Measurable g)
    (_ : ∀ᵐ ω ∂μ, (E.OPTagg c ω - E.ALG c ω).toENNReal ≤ g ω), ∫⁻ ω, g ω ∂μ

end Execution

end UnobservedWelfare


