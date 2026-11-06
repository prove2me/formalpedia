-- Prove2me | Definitions.Def_RiskDistMDP_DPP_Assumption213
-- name    : RiskDistMDP_DPP_Assumption213
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:55:30.11499+00:00
-- url     : https://prove2.me/theorems/a4bd8c0f-37a3-4e6e-8d50-6b4a69397111
-- title:
--   Assumption 2.13 — weak continuity, upper hemicontinuity, lower semicontinuity, bounded costs
-- statement:
--   **Assumption 2.13.** For every $t\in\mathbb N$:
--
--   1. (`A213i`) $(x,a)\mapsto P(t,x,a,\cdot)$ is weakly continuous;
--   2. (`A213ii`) $\bigcup_{x\in\mathbb X}\mathcal A_t(x)$ is compact, and $\mathcal A_t$ is upper hemicontinuous: for every $x$ and open $U\supseteq\mathcal A_t(x)$ there is an open $V\ni x$ with $\mathcal A_t(z)\subseteq U$ for $z\in V$;
--   3. (`A213iii`) for compact $K\subset\mathbb R$, $\mu^n\in\mathcal P(K)$ converging weakly to $\mu^0\in\mathcal P(K)$ and $x^n\to x^0$, $\liminf_n\sigma_{t,x^n}(\mu^n)\ge\sigma_{t,x^0}(\mu^0)$;
--   4. (`A213iv`) $C_t$ is lower semicontinuous and $\|C_t\|_\infty\le b_t$ for some $b_t>0$.
--
--   These are the conditions under which the Bellman operator preserves lower semicontinuity and admits measurable minimizers.
--
--   **Formalization Note** (i) is continuity into `ProbabilityMeasure 𝕏`. The page's sequential display has $\int_{\mathbb R}$ and $P(t,x,a,dy)$ on the right; these are read as $\int_{\mathbb X}$ and $P(t,x^0,a^0,dy)$, and on the metrizable $\mathbb X\times\mathbb A$ the sequential and topological forms agree. Upper hemicontinuity in (ii) is the published definition `CoupledLearning.IsUHC` on the whole space. In (iv) the bound is a function $b:\mathbb N\to\mathbb R$ of $t$, as printed; the infinite-horizon results use a constant function.
-- source:
--   Cheng & Jaimungal, Risk-Averse Markov Decision Processes through a Distributional Lens, arXiv:2203.09612v4, Assumption 2.13, p. 14

import Mathlib
import Definitions.Def_RiskDistMDP_DPP_RiskMDP
import Definitions.Def_CoupledLearning_IsUHC

set_option autoImplicit false

open MeasureTheory Filter Topology

namespace RiskDistMDP.DPP

/-- Assumption 2.13 (i) (arXiv:2203.09612v4, p.14): for every `t ∈ ℕ`, `(x, a) ↦ P(t, x, a, ·)` is
weakly continuous.

**Formalization Note** Stated as continuity into `ProbabilityMeasure 𝕏` with the topology of weak
convergence. The page's sequential form (`x^n → x⁰`, `a^n → a⁰` implies `∫ f dP(t,x^n,a^n,·) →
∫ f dP(t,x⁰,a⁰,·)` for `f ∈ C_b(𝕏)`; the printed `∫_ℝ` and `P(t,x,a,dy)` on the right are read as
`∫_𝕏` and `P(t,x⁰,a⁰,dy)`, reading R4) is equivalent because `𝕏 × 𝔸` is metrizable. -/
def A213i {𝕏 𝔸 : Type*} [MeasurableSpace 𝕏] [MeasurableSpace 𝔸] [TopologicalSpace 𝕏]
    [TopologicalSpace 𝔸] [OpensMeasurableSpace 𝕏] (M : BorelMDP 𝕏 𝔸) : Prop :=
  ∀ t, 1 ≤ t → Continuous fun p : 𝕏 × 𝔸 => M.P t p.1 p.2

/-- Assumption 2.13 (ii) (arXiv:2203.09612v4, p.14): for every `t ∈ ℕ`, `⋃_{x∈𝕏} 𝒜_t(x)` is
compact and `𝒜_t` is upper hemi-continuous: at every `x`, for every open `U ⊇ 𝒜_t(x)` there is an
open `V ∋ x` with `𝒜_t(z) ⊆ U` for `z ∈ V`.

**Formalization Note** Upper hemicontinuity is the published `CoupledLearning.IsUHC` on the whole
space (`D = univ`): for every open `U ⊇ 𝒜_t(x)`, eventually in `𝓝 x`, `𝒜_t(z) ⊆ U`, which is the
open-neighbourhood form of the page. -/
def A213ii {𝕏 𝔸 : Type*} [MeasurableSpace 𝕏] [MeasurableSpace 𝔸] [TopologicalSpace 𝕏]
    [TopologicalSpace 𝔸] (M : BorelMDP 𝕏 𝔸) : Prop :=
  ∀ t, 1 ≤ t → IsCompact (⋃ x, M.adm t x) ∧ CoupledLearning.IsUHC Set.univ (M.adm t)

/-- Assumption 2.13 (iii) (arXiv:2203.09612v4, p.14): for every `t ∈ ℕ`, compact `K ⊂ ℝ`,
`(μ^n) ⊂ 𝒫_b(K)` converging weakly to `μ⁰ ∈ 𝒫(K)` and `x^n → x⁰` in `𝕏`,
`liminf_n σ_{t,x^n}(μ^n) ≥ σ_{t,x⁰}(μ⁰)`.

**Formalization Note** `𝒫(K)` is the set of probability measures on `ℝ` carried by `K`; weak
convergence is convergence in `ProbabilityMeasure ℝ`. -/
def A213iii {𝕏 : Type*} [TopologicalSpace 𝕏] (σ : ℕ → 𝕏 → Measure ℝ → EReal) : Prop :=
  ∀ t, 1 ≤ t → ∀ K : Set ℝ, IsCompact K →
    ∀ (μs : ℕ → ProbabilityMeasure ℝ) (μ0 : ProbabilityMeasure ℝ) (xs : ℕ → 𝕏) (x0 : 𝕏),
      (∀ n, (μs n : Measure ℝ) Kᶜ = 0) → (μ0 : Measure ℝ) Kᶜ = 0 →
      Tendsto μs atTop (𝓝 μ0) → Tendsto xs atTop (𝓝 x0) →
      σ t x0 (μ0 : Measure ℝ) ≤ liminf (fun n => σ t (xs n) (μs n : Measure ℝ)) atTop

/-- Assumption 2.13 (iv) (arXiv:2203.09612v4, p.14): for every `t ∈ ℕ`, the cost function `C_t` is
lower semicontinuous and `‖C_t‖_∞ ≤ b_t` with `b_t > 0`.

**Formalization Note** The bound is a function `b : ℕ → ℝ` of `t`, as printed ("for any `t`:
… `≤ b` for some `b > 0`"). The infinite-horizon results of §5 use one constant for all `t`
(they bound values by `b/(1−γ)`); they apply this with the constant function `fun _ => b`. -/
def A213iv {𝕏 𝔸 : Type*} [MeasurableSpace 𝕏] [MeasurableSpace 𝔸] [TopologicalSpace 𝕏]
    [TopologicalSpace 𝔸] (M : BorelMDP 𝕏 𝔸) (b : ℕ → ℝ) : Prop :=
  ∀ t, 1 ≤ t → LowerSemicontinuous (fun p : 𝕏 × 𝔸 × 𝕏 => M.C t p.1 p.2.1 p.2.2) ∧ 0 < b t ∧
    ∀ x a y, |M.C t x a y| ≤ b t

/-- **Assumption 2.13** (arXiv:2203.09612v4, p.14): (i), (ii), (iii) and (iv), with cost bounds
`b t`. -/
def Assumption213 {𝕏 𝔸 : Type*} [MeasurableSpace 𝕏] [MeasurableSpace 𝔸] [TopologicalSpace 𝕏]
    [TopologicalSpace 𝔸] [OpensMeasurableSpace 𝕏] (R : RiskMDP 𝕏 𝔸) (b : ℕ → ℝ) : Prop :=
  A213i R.toBorelMDP ∧ A213ii R.toBorelMDP ∧ A213iii R.σ ∧ A213iv R.toBorelMDP b

end RiskDistMDP.DPP


