-- Prove2me | Definitions.Def_ResolvingPricing_Run
-- name    : ResolvingPricing_Run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:25:42.032514+00:00
-- url     : https://prove2.me/theorems/84a4707f-2073-40d6-b26d-de01b740457b
-- title:
--   Admissible pricing run, inventory, revenue, the resolving heuristic and harmonic series
-- statement:
--   Fix a model, a horizon $T$ and a normalized initial inventory $x_T$, so the initial inventory is $y_T=x_T T$. Periods are indexed backward, $t=T,\dots,1$. A **run** on a probability space $(\Omega,\mathcal F,\mathbb P)$ with a filtration consists of demand rates $\lambda_t\in[\underline d,\bar d]$ and noises $\xi_t$ such that
--   1. $\lambda_t$ is measurable with respect to $\mathcal F_{t+1}$, the history up to the previous period (the policy is **admissible**);
--   2. $\xi_t$ is adapted, and given $\mathcal F_{t+1}$ it has law $Q(\lambda_t)$.
--
--   With demand $d_t=\lambda_t+\xi_t$, the sales are $s_t=\min\{d_t,y_t\}$, the lost sales $\ell_t=(d_t-y_t)^+$, the inventory evolves by $y_{t-1}=y_t-s_t$, and the revenue is $\sum_{t=1}^T f^{-1}(\lambda_t)s_t$. Its expectation is the **expected revenue** $R^\pi(T,x_T)$.
--
--   The run **follows the resolving heuristic** if, whenever the normalized inventory $x_t=y_t/t$ satisfies $x_t\ge\underline d$, it chooses $\lambda_t=\min\{x_t,\lambda^u\}$.
--
--   Along a run, $\Delta_t=\lambda_t-x_t$, and the **harmonic series** of a sequence $a$ is
--   $$\bar a_{\to t}=\frac{a_T}{T-1}+\frac{a_{T-1}}{T-2}+\dots+\frac{a_{t+1}}{t},\qquad \bar a_{\to T}=0.$$
--
--   These are the processes compared in the goal theorem and its milestones.
--
--   **Formalization Note** Time runs forward in Lean: step $k$ is the paper's period $t=T-k$, and the filtration index $k$ is the paper's $\mathcal F_{t+1}$. The conditional law is stated through conditional expectations of indicators of Borel sets. Below $\underline d$ the fluid problem is infeasible and the paper leaves the resolving heuristic undefined; a resolving run may then choose any admissible demand rate. The harmonic series at $t=0$ would contain $a_1/0$, which Lean evaluates as $0$; no statement uses it.
-- source:
--   Y. Wang, H. Wang, Constant Regret Resolving Heuristics for Price-Based Revenue Management, Oper. Res. 70(6):3538–3557 (2022), doi:10.1287/opre.2021.2219, §1 p.3538 ((1)–(3), admissible policies); §3 p.3541 (A4, resolving heuristic); §4.1 p.3543 (x_τ, Δ_τ, ℓ_τ, harmonic series, resolving rule above λᵘ)

import Mathlib
import Definitions.Def_ResolvingPricing_Model

open MeasureTheory

namespace ResolvingPricing

/-- **An admissible run of a pricing policy**, Wang & Wang, Oper. Res. 70(6) (2022), §1, p.3538
(model (1)–(3), admissible policies) and §3, p.3541 (A4).

On a measurable space `Ω` with a measure `μ` and a filtration `ℱ`, a run over `T` periods from the
normalized initial inventory `x` (initial inventory `y_T = x T`) consists of

1. the demand rates `lam k`, with values in `[d̲, d̄]` and `ℱ k`-measurable (the posted price
   `f⁻¹(lam k)` depends only on the history up to the previous period: admissibility);
2. the demand noises `ξ k`, `ℱ (k+1)`-measurable (the noise is adapted);
3. the conditional law of the noise given the past: for every Borel set `S`,
   `μ[ξ_k ∈ S | ℱ k] = Q(lam k)(S)` almost surely.

**Formalization Note.** Time runs forward: `k = 0, …, T − 1` is the paper's period `t = T − k`, so
`ℱ k` is the paper's `ℱ_{t+1}` (the history up to the previous period). A4's "conditional
distribution of `ξ_t` given `p_t` is `Q(p_t)`" is read as the law of `ξ_t` given the whole past
`ℱ_{t+1}` (it is how the Bellman equation (5) and the recursion (7) use it); the mean-zero and
boundedness parts of A4 then follow from `Model.Assumptions`. The run may randomize: `ℱ 0` need not be
trivial. Nothing is required of `lam k`, `ξ k` for `k ≥ T`. -/
structure Run (P : Model) (T : ℕ) (x : ℝ) {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    (ℱ : Filtration ℕ mΩ) where
  /-- The demand rate chosen in forward step `k` (period `T − k`). -/
  lam : ℕ → Ω → ℝ
  /-- The demand noise in forward step `k` (period `T − k`). -/
  ξ : ℕ → Ω → ℝ
  lam_mem : ∀ k < T, ∀ ω, lam k ω ∈ P.D
  lam_measurable : ∀ k < T, Measurable[ℱ k] (lam k)
  ξ_measurable : ∀ k < T, Measurable[ℱ (k + 1)] (ξ k)
  law : ∀ k < T, ∀ S : Set ℝ, MeasurableSet S →
    μ[(ξ k ⁻¹' S).indicator (fun _ => (1 : ℝ)) | ℱ k] =ᵐ[μ] fun ω => (P.Q (lam k ω) S).toReal

namespace Run

variable {P : Model} {T : ℕ} {x : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {ℱ : Filtration ℕ mΩ}

/-- The inventory at the start of forward step `k` (the paper's `y_{T−k}`), by (1)–(2): sales are
`min(d, y)` for demand `d = lam k + ξ k`, and the inventory decreases by the sales. -/
noncomputable def inv (ρ : Run P T x μ ℱ) : ℕ → Ω → ℝ
  | 0 => fun _ => x * T
  | k + 1 => fun ω => ρ.inv k ω - min (ρ.lam k ω + ρ.ξ k ω) (ρ.inv k ω)

/-- The realized total revenue `∑_t r_t = ∑_t p_t s_t` of the run, (2). -/
noncomputable def revenue (ρ : Run P T x μ ℱ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range T, P.g (ρ.lam k ω) * min (ρ.lam k ω + ρ.ξ k ω) (ρ.inv k ω)

/-- The expected revenue `R^π(T, x_T)` of (3). -/
noncomputable def expRevenue (ρ : Run P T x μ ℱ) : ℝ := ∫ ω, ρ.revenue ω ∂μ

/-- **The run follows the resolving heuristic** `πʳ` (pp.3541 and 3543): whenever the normalized
inventory `x_t = y_t / t` is at least `d̲`, the chosen demand rate is the fluid optimum
`min{x_t, λᵘ}` (price `f⁻¹(min{x_t, λᵘ})`).

**Formalization Note.** Below `d̲` the fluid problem `max{r(λ) : λ ∈ [d̲, d̄], λ ≤ x_t}` has no feasible
point and the paper does not define `πʳ`; there the run may choose any admissible demand rate. -/
def IsResolving (ρ : Run P T x μ ℱ) : Prop :=
  ∀ k < T, ∀ ω, P.dlo ≤ ρ.inv k ω / ((T - k : ℕ) : ℝ) →
    ρ.lam k ω = min (ρ.inv k ω / ((T - k : ℕ) : ℝ)) P.lamU

/-! ### Path quantities in the paper's backward period index `τ = T − k` (p.3543) -/

/-- `y_τ`, the inventory at the start of period `τ` (`y_0` is the final inventory). -/
noncomputable def yB (ρ : Run P T x μ ℱ) (τ : ℕ) (ω : Ω) : ℝ := ρ.inv (T - τ) ω

/-- `x_τ = y_τ / τ`, the normalized inventory at period `τ ≥ 1`. -/
noncomputable def xB (ρ : Run P T x μ ℱ) (τ : ℕ) (ω : Ω) : ℝ := ρ.yB τ ω / τ

/-- `λ_τ`, the demand rate chosen in period `τ`. -/
def lamB (ρ : Run P T x μ ℱ) (τ : ℕ) (ω : Ω) : ℝ := ρ.lam (T - τ) ω

/-- `ξ_τ`, the demand noise of period `τ`. -/
def xiB (ρ : Run P T x μ ℱ) (τ : ℕ) (ω : Ω) : ℝ := ρ.ξ (T - τ) ω

/-- `ℓ_τ = (λ_τ + ξ_τ − y_τ)⁺`, the lost sales of period `τ`. -/
noncomputable def lostB (ρ : Run P T x μ ℱ) (τ : ℕ) (ω : Ω) : ℝ :=
  max (ρ.lamB τ ω + ρ.xiB τ ω - ρ.yB τ ω) 0

/-- `Δ_τ = λ_τ − x_τ` (p.3543). -/
noncomputable def DeltaB (ρ : Run P T x μ ℱ) (τ : ℕ) (ω : Ω) : ℝ := ρ.lamB τ ω - ρ.xB τ ω

end Run

/-- **The harmonic series** of p.3543: for a sequence `a` indexed by periods,
`ā→t = a_T/(T − 1) + a_{T−1}/(T − 2) + … + a_{t+1}/t = ∑_{j=t+1}^{T} a_j/(j − 1)`, with `ā→T = 0`.

**Formalization Note.** For `t ≥ 1` no denominator vanishes. At `t = 0` the term `a_1/0` is `0` in
Lean; the paper never uses `ā→0`, and no statement of the mission depends on its value. -/
noncomputable def harm (T : ℕ) (a : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ioc t T, a j / ((j : ℝ) - 1)

end ResolvingPricing


