-- Prove2me | Definitions.Def_UnobservedWelfare_Supplement_CausalAllocation
-- name    : UnobservedWelfare_Supplement_CausalAllocation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:19:07.385754+00:00
-- url     : https://prove2.me/theorems/2037e489-de38-413e-a9d0-c2d52f41b0b5
-- title:
--   Feasible causal policies, inventory, $\mathrm{ALG}_T$ and $\mathrm{OPT}^{\mathrm{agg}}_T$ (§7)
-- statement:
--   Fix $m$ goods, a horizon $T$, a type space $\Theta$ with type distribution $P$, and a probability space $(\Omega,\mu)$. A **run of a feasible causal policy** consists of
--
--   1. buyer types $\theta_1,\dots,\theta_T$, i.i.d. with law $P$;
--   2. a $\sigma$-algebra $\mathcal F_0$ carrying the policy's own randomness $\omega$, independent of all types;
--   3. productions $q_t\in[0,1]^m$ and allocations $X_t\ge0$, both measurable with respect to $\sigma(\omega,\theta_1,\dots,\theta_t)$: they may depend on the current type, and are chosen directly, with no prices and no demand constraint.
--
--   The inventory is $I_0=0$, $I_t=\sum_{s\le t}(q_s-X_s)$, and the run is **feasible** if $I_t\ge0$ for every $t\in[T]$ on every path. For utilities $u_\theta$ and a production cost $c$, the online welfare and the aggregate offline benchmark are
--
--   $$\mathrm{ALG}_T=\sum_{t=1}^T u_{\theta_t}(X_t)-\sum_{t=1}^T c(q_t),\qquad \mathrm{OPT}^{\mathrm{agg}}_T=\sup\Big\{\sum_{t}u_{\theta_t}(x_t)-\sum_t c(\bar q_t)\ :\ x_t\ge0,\ \bar q_t\in[0,1]^m,\ \sum_t x_t\le\sum_t\bar q_t\Big\}.$$
--
--   This is the enlarged policy class of the lower bound of §7: it contains the purchase-based policies of §2 and policies that know the type distribution and observe the current type before allocating.
--
--   **Formalization Note** Rounds are 0-based (Lean round $k$ is the paper's round $t=k+1$). Utilities are `EReal`-valued, as in the base mission's `IsRC` file, whose `cube` and `posOrthant` are reused. The structure has the same seed and independence encoding as the base `Execution`.
-- source:
--   Cheng–Tao–Xing, Maximizing Unobserved Welfare: Logarithmic Regret from Purchases, manuscript (STOC 2027 submission; held artifact sha256 cfd42fa2b0b4d51bad26ff5715acac275b66e830e1391d884542854ddde215fe), policy class in the proof of Theorem 7.1, p.35 (PDF p.37); inventory (26), p.16 (PDF p.18); (31), (32), p.18 (PDF p.20)

import Mathlib
import Definitions.Def_UnobservedWelfare_IsRC

open MeasureTheory ProbabilityTheory Matrix

namespace UnobservedWelfare.Supplement

/-- One run of a **feasible causal policy** of Cheng–Tao–Xing, *Maximizing Unobserved Welfare:
Logarithmic Regret from Purchases*, manuscript (STOC 2027 submission), proof of Theorem 7.1, p.35
(PDF p.37), on a probability space `(Ω, μ)`, for horizon `T` and `m` goods.

* `θ k` is the type of the buyer of (0-based) round `k`, the paper's `θ_{k+1} = V_{k+1}`;
  `θ 0, …, θ (T-1)` are i.i.d. with law `P`.
* `F0` is the σ-algebra of the policy's randomness `ω`, independent of all types.
* `q k` and `X k` are the production and the allocation of round `k`. Both may depend on the
  types of rounds `0, …, k` (the current type included) and on `ω`: they are measurable with
  respect to `F0 ⊔ σ(θ 0, …, θ k)`. Production lies in `[0,1]^m` and the allocation is `≥ 0` on
  every path. There are no prices and no demand constraint: allocations are chosen directly.

**Formalization Note** This is the enlarged policy class of p.35. It contains the purchase-based
executions `UnobservedWelfare.Execution` of §2 (there `q k` sees only the past and `X k` lies in a
demand set), and policies that know the type distribution (the structure is formed after `P`).
Rounds are 0-based: Lean round `k < T` is the paper's round `t = k + 1`. The inventory constraint is
the separate predicate `IsFeasible`. -/
structure CausalAllocation (m T : ℕ) {Θ : Type*} [MeasurableSpace Θ] (P : Measure Θ)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) where
  θ : ℕ → Ω → Θ
  measurable_θ : ∀ k, Measurable (θ k)
  law : ∀ k < T, μ.map (θ k) = P
  iIndep : iIndepFun (fun k : Fin T => θ k) μ
  F0 : MeasurableSpace Ω
  F0_le : F0 ≤ mΩ
  indep_seed : Indep F0 (⨆ k : Fin T, MeasurableSpace.comap (θ k) inferInstance) μ
  q : ℕ → Ω → (Fin m → ℝ)
  X : ℕ → Ω → (Fin m → ℝ)
  measurable_q : ∀ k < T,
    Measurable[F0 ⊔ ⨆ (j : ℕ) (_ : j ≤ k), MeasurableSpace.comap (θ j) inferInstance] (q k)
  measurable_X : ∀ k < T,
    Measurable[F0 ⊔ ⨆ (j : ℕ) (_ : j ≤ k), MeasurableSpace.comap (θ j) inferInstance] (X k)
  q_mem : ∀ k < T, ∀ ω, q k ω ∈ cube m
  X_nonneg : ∀ k < T, ∀ ω, 0 ≤ X k ω

namespace CausalAllocation

variable {m T : ℕ} {Θ : Type*} [MeasurableSpace Θ] {P : Measure Θ}
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The remaining inventory `I_n = Σ_{t ≤ n} (q_t − X_t)` after the first `n` rounds, with
`I_0 = 0` (Cheng–Tao–Xing manuscript, (26), p.16 (PDF p.18)); `n` is the paper's index. -/
def invAfter (E : CausalAllocation m T P μ) (n : ℕ) (ω : Ω) : Fin m → ℝ :=
  ∑ j ∈ Finset.range n, (E.q j ω - E.X j ω)

/-- Feasibility, the inventory constraints of (26) (Cheng–Tao–Xing manuscript, p.16 (PDF p.18);
"subject to the inventory constraints", p.35 (PDF p.37)): `I_t ≥ 0` for every `t ∈ [T]` on every
path. -/
def IsFeasible (E : CausalAllocation m T P μ) : Prop :=
  ∀ n, 1 ≤ n → n ≤ T → ∀ ω, 0 ≤ E.invAfter n ω

/-- Realized online welfare `ALG_T = Σ_t u_{θ_t}(X_t) − Σ_t c(q_t)` (Cheng–Tao–Xing manuscript,
(31), p.18 (PDF p.20)), for utilities `u` and production cost `c`. -/
noncomputable def ALG (E : CausalAllocation m T P μ) (u : Θ → (Fin m → ℝ) → EReal)
    (c : (Fin m → ℝ) → ℝ) (ω : Ω) : EReal :=
  (∑ k ∈ Finset.range T, u (E.θ k ω) (E.X k ω)) - ((∑ k ∈ Finset.range T, c (E.q k ω) : ℝ) : EReal)

/-- The aggregate offline benchmark (Cheng–Tao–Xing manuscript, (32), p.18 (PDF p.20)):
`OPT^agg_T = sup { Σ_t u_{θ_t}(x_t) − Σ_t c(q̄_t) : x_t ≥ 0, q̄_t ∈ [0,1]^m, Σ_t x_t ≤ Σ_t q̄_t }`.
Its intermediate inventory need not be nonnegative. -/
noncomputable def OPTagg (E : CausalAllocation m T P μ) (u : Θ → (Fin m → ℝ) → EReal)
    (c : (Fin m → ℝ) → ℝ) (ω : Ω) : EReal :=
  ⨆ (x : Fin T → Fin m → ℝ) (qb : Fin T → Fin m → ℝ)
    (_ : (∀ k, 0 ≤ x k) ∧ (∀ k, qb k ∈ cube m) ∧ ∑ k, x k ≤ ∑ k, qb k),
    (∑ k : Fin T, u (E.θ k ω) (x k)) - ((∑ k : Fin T, c (qb k) : ℝ) : EReal)

end CausalAllocation

end UnobservedWelfare.Supplement


