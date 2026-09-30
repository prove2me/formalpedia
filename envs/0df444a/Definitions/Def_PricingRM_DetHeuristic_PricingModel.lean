-- Prove2me | Definitions.Def_PricingRM_DetHeuristic_PricingModel
-- name    : PricingRM_DetHeuristic_PricingModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T19:32:47.740733+00:00
-- url     : https://prove2.me/theorems/79fc3bf1-9b96-4dee-9d81-69c1b9d0b187
-- title:
--   N-period single-product pricing model with price-dependent random demand, its Bellman value, the deterministic problem (32)–(33) and the fixed-price heuristic
-- statement:
--   This definition file sets up the periodic-review pricing model of Bitran and Caldentey (2003, §3.2.1) and every quantity that Proposition 8 and its proof refer to.
--
--   **Model.** A single product is sold over $N$ periods $n = 1, \dots, N$. In period $n$ the seller charges a price $p \ge 0$, and the demand $D_n(p)$ is a random variable whose law $\mu_n(p)$ is a probability measure carried by $[0,\infty)$ with finite mean. The law may depend on $n$ and on $p$ in an arbitrary way. With inventory $C$ and demand $D$ the seller sells $\min\{D, C\}$ and keeps $C - \min\{D, C\}$; unmet demand is lost. The mean demand is written $E[D_n(p)]$.
--
--   **Optimal expected revenue.** The value functions are defined by the Bellman recursion of the paper's Appendix: $V_{N+1} \equiv 0$ and, for $n = N, N-1, \dots, 1$,
--   $$
--   V_n(C) = \sup_{p \ge 0} E\big[p\min\{D_n(p), C\} + V_{n+1}\big(C - \min\{D_n(p), C\}\big)\big].
--   $$
--   $V_1(C_0)$ is the optimal expected revenue with initial inventory $C_0$. The recursion uses one period's demand law at a time, which is the independent-periods reading of the model.
--
--   **Deterministic problem (32)–(33).** For a price vector $p = (p_1, \dots, p_N)$, the objective is $\sum_{n=1}^N p_n E[D_n(p_n)]$, and $p$ is feasible for capacity $C$ if $p_n \ge 0$ for all $n$ and $\sum_{n=1}^N E[D_n(p_n)] \le C$. The optimal value is
--   $$
--   V_1^{\det}(C) = \sup\Big\{\sum_{n=1}^N p_n E[D_n(p_n)] \;:\; p \in [0,\infty)^N,\ \sum_{n=1}^N E[D_n(p_n)] \le C\Big\},
--   $$
--   equal to $-\infty$ if no price vector is feasible and $+\infty$ if the objective is unbounded. A feasible $p$ whose objective is at least that of every feasible vector is an optimal solution.
--
--   **Certainty-equivalent value (24).** For one period $n$ and capacity $C$, $\sup_{p\ge 0} p\min\{E[D_n(p)], C\}$.
--
--   **Deterministic-price heuristic.** Charging fixed prices $p_1,\dots,p_N$ regardless of sales, the demands $D_1(p_1), \dots, D_N(p_N)$ are independent. With cumulative demand $\mathscr{D}_n = \sum_{i=1}^n D_i(p_i)$, $\mathscr{D}_0 = 0$, the expected revenue is
--   $$
--   V_1(p, C_0) = \sum_{n=1}^N p_n E\Big[D_n(p_n) - \big(D_n(p_n) - (C_0 - \mathscr{D}_{n-1})^+\big)^+\Big],
--   $$
--   i.e. period $n$ sells $\min\{D_n(p_n), (C_0 - \mathscr{D}_{n-1})^+\}$. Finally $\sigma_n^2 = \operatorname{Var}(\mathscr{D}_n)$,
--   $$
--   \eta_n(C_0) = \frac{\sqrt{\sigma_n^2 + (C_0 - E[\mathscr{D}_n])^2} - (C_0 - E[\mathscr{D}_n])}{2}, \qquad \nu = \frac{\sigma_N}{E[\mathscr{D}_N]}
--   $$
--   are the quantities of eq. (34) and of (36), evaluated at the price vector $p$ (the paper evaluates them at $p^{\det}$).
--
--   These objects are shared by every statement of the mission: the goal (Proposition 8, eq. (35)) and all milestones are stated about exactly these value functions and this heuristic revenue.
--
--   **Formalization Note** Periods are indexed by `Fin N` ($0, \dots, N-1$ for the paper's $1, \dots, N$). Demand laws are `μ n p : Measure ℝ`; the axioms (probability measure, almost surely nonnegative, integrable) are required at every real price, which is harmless because laws at negative prices never enter a statement. The Bellman value `valueToGo M k _ C` has `k` periods remaining, so the paper's $V_n$ is `valueToGo M (N - n + 1)`, and `optValue M C₀ = V_1(C₀)`; it is computed in $[0,\infty]$ with the lower Lebesgue integral and `⨆`, so no supremum takes a junk value (the integrand is monotone in the demand, hence measurable). $V_1^{\det}$ is `detValue`, an `EReal` supremum over the feasible subtype ($\bot$ if infeasible). The heuristic's joint law is the product measure `Measure.pi`, which encodes independence. Variances are Mathlib's `variance`; statements that use them assume square integrability. The typo $\mathscr{D}_n^{\det} := \sum_{i=1}^n D_n(p^{\det})$ on p. 221 is read as $\sum_{i=1}^n D_i(p_i^{\det})$, as the Appendix uses it.
-- source:
--   Bitran and Caldentey, An Overview of Pricing Models for Revenue Management, MSOM 5(3) 2003, p. 221, Section 3.2.1, eqs. (32)–(34); p. 217, eqs. (22), (24); Appendix, Proof of Proposition 8, p. 227 (Bellman recursion and V_1(p^det, C_0))

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PricingRM.DetHeuristic

/-- The `N`-period single-product pricing model with price-dependent random demand
(Bitran–Caldentey 2003, §3.2.1, p. 221). Periods are indexed `0, …, N-1` (the paper's
`1, …, N`). `μ n p` is the law of the demand `D_n(p)` of period `n` at price `p`: a probability
measure on `ℝ`, carried by `[0, ∞)`, with finite mean. The law may depend on `n` and `p` in any
way. Laws at negative prices never enter any statement. -/
structure PricingModel (N : ℕ) where
  /-- `μ n p` is the law of the demand `D_n(p)`. -/
  μ : Fin N → ℝ → Measure ℝ
  isProb : ∀ n p, IsProbabilityMeasure (μ n p)
  nonneg : ∀ n p, ∀ᵐ x ∂(μ n p), 0 ≤ x
  integrable : ∀ n p, Integrable (fun x : ℝ => x) (μ n p)

instance {N : ℕ} (M : PricingModel N) (n : Fin N) (p : ℝ) :
    IsProbabilityMeasure (M.μ n p) :=
  M.isProb n p

/-- The mean demand `E[D_n(p)]`. -/
noncomputable def meanDemand {N : ℕ} (M : PricingModel N) (n : Fin N) (p : ℝ) : ℝ :=
  ∫ x, x ∂(M.μ n p)

/-- Bellman value with `k` periods remaining (periods `N-k, …, N-1`, 0-based) and inventory `C`:
`valueToGo M 0 _ C = 0` and
`valueToGo M (k+1) _ C = ⨆_{p ≥ 0} E[p·min{D(p), C} + valueToGo M k _ (C - min{D(p), C})]`,
where `D(p)` has law `μ (N-k-1) p`. In the paper's notation this is `V_{N-k+1}(C)`
(Appendix, p. 227), computed in `ℝ≥0∞` so that the supremum is never a junk value. -/
noncomputable def valueToGo {N : ℕ} (M : PricingModel N) : (k : ℕ) → k ≤ N → ℝ → ℝ≥0∞
  | 0, _, _ => 0
  | k + 1, hk, C => ⨆ p ∈ Set.Ici (0 : ℝ),
      ∫⁻ x, (ENNReal.ofReal (p * min x C) + valueToGo M k (Nat.le_of_succ_le hk) (C - min x C))
        ∂(M.μ ⟨N - (k + 1), by omega⟩ p)

/-- The optimal expected revenue `V_1(C)` over all `N` periods with initial inventory `C`. -/
noncomputable def optValue {N : ℕ} (M : PricingModel N) (C : ℝ) : ℝ≥0∞ :=
  valueToGo M N le_rfl C

/-- Objective (32) of the deterministic problem: `∑_n p_n E[D_n(p_n)]`. -/
noncomputable def detObjective {N : ℕ} (M : PricingModel N) (p : Fin N → ℝ) : ℝ :=
  ∑ n, p n * meanDemand M n (p n)

/-- Feasible region of the deterministic problem: nonnegative prices satisfying (33),
`∑_n E[D_n(p_n)] ≤ C`. -/
def DetFeasible {N : ℕ} (M : PricingModel N) (C : ℝ) (p : Fin N → ℝ) : Prop :=
  (∀ n, 0 ≤ p n) ∧ ∑ n, meanDemand M n (p n) ≤ C

/-- `p` is an optimal solution of the deterministic problem (32)–(33) with capacity `C`. -/
def IsDetOptimal {N : ℕ} (M : PricingModel N) (C : ℝ) (p : Fin N → ℝ) : Prop :=
  DetFeasible M C p ∧ ∀ q, DetFeasible M C q → detObjective M q ≤ detObjective M p

/-- Optimal value `V_1^det(C)` of (32)–(33), as a supremum in `EReal`: `⊥` if infeasible,
`⊤` if unbounded. -/
noncomputable def detValue {N : ℕ} (M : PricingModel N) (C : ℝ) : EReal :=
  ⨆ q : {q : Fin N → ℝ // DetFeasible M C q}, ((detObjective M q.1 : ℝ) : EReal)

/-- Certainty-equivalent single-period value of (24): `⨆_{p ≥ 0} p·min{E[D_n(p)], C}`. -/
noncomputable def ceValue {N : ℕ} (M : PricingModel N) (n : Fin N) (C : ℝ) : ℝ≥0∞ :=
  ⨆ p ∈ Set.Ici (0 : ℝ), ENNReal.ofReal (p * min (meanDemand M n p) C)

/-- Joint law of the demands `(D_1(p_1), …, D_N(p_N))` under the fixed price vector `p`:
the periods' demands are independent. -/
noncomputable def heuristicLaw {N : ℕ} (M : PricingModel N) (p : Fin N → ℝ) :
    Measure (Fin N → ℝ) :=
  Measure.pi fun n => M.μ n (p n)

/-- Cumulative demand strictly before period `n`: the paper's `𝒟_{n-1}`. -/
def cumDemandBefore {N : ℕ} (x : Fin N → ℝ) (n : Fin N) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => i < n), x i

/-- Cumulative demand up to and including period `n`: the paper's `𝒟_n`. -/
def cumDemand {N : ℕ} (x : Fin N → ℝ) (n : Fin N) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => i ≤ n), x i

/-- Expected revenue `V_1(p, C_0)` of charging the fixed prices `p` (p. 227):
`∑_n p_n E[D_n - (D_n - (C_0 - 𝒟_{n-1})^+)^+]`, i.e. period `n` sells
`min{D_n, (C_0 - 𝒟_{n-1})^+}`, under independent demands. -/
noncomputable def heuristicRevenue {N : ℕ} (M : PricingModel N) (C₀ : ℝ) (p : Fin N → ℝ) : ℝ :=
  ∑ n, p n * ∫ x, (x n - max (x n - max (C₀ - cumDemandBefore x n) 0) 0) ∂(heuristicLaw M p)

/-- Mean `E[𝒟_n]` of the cumulative demand under the prices `p`. -/
noncomputable def cumMean {N : ℕ} (M : PricingModel N) (p : Fin N → ℝ) (n : Fin N) : ℝ :=
  ∫ x, cumDemand x n ∂(heuristicLaw M p)

/-- Variance `σ_n^2 = Var(𝒟_n)` of the cumulative demand under the prices `p`. -/
noncomputable def cumVariance {N : ℕ} (M : PricingModel N) (p : Fin N → ℝ) (n : Fin N) : ℝ :=
  variance (fun x => cumDemand x n) (heuristicLaw M p)

/-- `η_n(C_0)` of (34): `(√(σ_n^2 + (C_0 - E[𝒟_n])^2) - (C_0 - E[𝒟_n])) / 2`. -/
noncomputable def eta {N : ℕ} (M : PricingModel N) (C₀ : ℝ) (p : Fin N → ℝ) (n : Fin N) : ℝ :=
  (Real.sqrt (cumVariance M p n + (C₀ - cumMean M p n) ^ 2) - (C₀ - cumMean M p n)) / 2

/-- Coefficient of variation `σ_n / E[𝒟_n]` of the cumulative demand; at the last period it is
the paper's `ν(C_0)`. -/
noncomputable def cumCV {N : ℕ} (M : PricingModel N) (p : Fin N → ℝ) (n : Fin N) : ℝ :=
  Real.sqrt (cumVariance M p n) / cumMean M p n

end PricingRM.DetHeuristic


