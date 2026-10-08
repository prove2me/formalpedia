-- Prove2me | Definitions.Def_DROOptimal_Continuous_Setting
-- name    : DROOptimal_Continuous_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T19:03:55.95581+00:00
-- url     : https://prove2.me/theorems/c15d21d8-c6f6-49d5-8c46-160b456d4cdf
-- title:
--   §2.2, §5, pp. 8–26 — 𝒫 on compact Ξ ⊆ ℜ^d (weak topology), c(x,ℙ), relative entropy I (Def. 8), ℙ̂_T, decay rates, 𝒞, feasibility and strong optimality in (5), ĉ_r, γ̄, Ξ⋆
-- statement:
--   This module fixes the continuous-state setting of §5 of Van Parys, Mohajerin Esfahani and Kuhn and the objects their results there are about.
--
--   The random parameter $\xi$ ranges over a set $\Xi\subseteq\mathbb R^d$ (assumed compact in every theorem), decisions $x$ range over $X\subseteq\mathbb R^n$, and $\gamma(x,\xi)$ is a cost. The module defines:
--
--   1. **Model class.** $\mathcal P$, the Borel probability distributions on $\Xi$, with the topology of weak convergence of distributions.
--   2. **Model-based predictor.** $c(x,\mathbb P)=\int_\Xi\gamma(x,\xi)\,\mathrm d\mathbb P(\xi)$.
--   3. **Relative entropy** (Definition 8). For $\mathbb P',\mathbb P\in\mathcal P$,
--   $$
--   I(\mathbb P',\mathbb P)=\begin{cases}\int_\Xi\log\frac{\mathrm d\mathbb P'}{\mathrm d\mathbb P}(\xi)\,\mathrm d\mathbb P'(\xi) & \text{if }\mathbb P'\ll\mathbb P,\\ +\infty&\text{otherwise,}\end{cases}
--   $$
--   a value in $[0,+\infty]$.
--   4. **Empirical distribution.** For a sample path $\xi_1,\dots,\xi_T$ with $T\ge1$, $\hat{\mathbb P}_T=\frac1T\sum_{t=1}^T\delta_{\xi_t}$.
--   5. **Sampling probability.** $\mathbb P^\infty(\hat{\mathbb P}_T\in\mathcal D)$, the probability that the empirical distribution of $T$ independent samples from $\mathbb P$ lies in $\mathcal D\subseteq\mathcal P$.
--   6. **Decay rates.** For $s\in[0,\infty]$ and a sequence $p_T\ge0$: $\limsup_{T\to\infty}\frac1T\log p_T\le -s$ holds if and only if for every finite $r'<s$ eventually $p_T\le e^{-r'T}$; and $\liminf_{T\to\infty}\frac1T\log p_T\ge -s$ holds if and only if for every finite $s'>s$ eventually $p_T\ge e^{-s'T}$ (with $\log0=-\infty$).
--   7. **Data-driven predictors** (the class $\mathcal C$). Functions $\hat c:X\times\mathcal P\to\mathbb R$ continuous for the product of the Euclidean topology on $X$ and the weak topology on $\mathcal P$.
--   8. **Problem (5).** $\hat c$ is *feasible* in (5) if $\hat c\in\mathcal C$ and, for all $x\in X$ and $\mathbb P\in\mathcal P$, the out-of-sample disappointment satisfies
--   $$
--   \limsup_{T\to\infty}\frac1T\log\mathbb P^\infty\big(c(x,\mathbb P)>\hat c(x,\hat{\mathbb P}_T)\big)\le -r .
--   $$
--   It is *strongly optimal* if it is feasible and $\hat c(x,\mathbb P')\le\hat c'(x,\mathbb P')$ for all $x,\mathbb P'$ and every feasible $\hat c'$.
--   9. **Distributionally robust predictor** (Definition 6, (10), with Definition 8). $\hat c_r(x,\mathbb P')=\sup_{\mathbb P\in\mathcal P}\{c(x,\mathbb P): I(\mathbb P',\mathbb P)\le r\}$.
--   10. **Worst case.** $\bar\gamma(x)=\max_{\xi\in\Xi}\gamma(x,\xi)$ and $\Xi^\star(x)=\arg\max_{\xi\in\Xi}\gamma(x,\xi)$.
--
--   The estimator realization $\mathbb P'$ is always the first argument of $I$.
--
--   **Formalization Note** $\mathcal P$ is `ProbabilityMeasure ↥Ξ` for the Borel σ-algebra of the subtype, with Mathlib's weak-convergence topology. $I$ is Mathlib's `klDiv`, valued in $[0,\infty]$: it is $\infty$ unless $\mathbb P'\ll\mathbb P$; when $\mathbb P'\ll\mathbb P$ it is $\int\log(\mathrm d\mathbb P'/\mathrm d\mathbb P)\,\mathrm d\mathbb P'$ if the log-likelihood ratio is $\mathbb P'$-integrable and $\infty$ otherwise, which is the paper's value since the negative part of the integrand is always integrable. The sampling probability is the product measure $\mathbb P^{\otimes T}$ of the set of sample paths (outer measure for a non-measurable set), and is set to $0$ at $T=0$; all statements are asymptotic in $T$. Decay rates are stated without logarithms, so that a probability vanishing for large $T$ has rate $-\infty$. For feasibility the threshold is $\max(r,0)$, which changes nothing since the condition is trivial for $r\le0$. $\hat c_r$, $\bar\gamma$ are real suprema; under the standing assumptions and $r\ge0$ the sets are nonempty and bounded above, and every theorem that uses them has a probability measure on $\Xi$ in scope, so $\Xi\neq\emptyset$. Mission 1 of this series defines the finite-state counterparts.
-- source:
--   Van Parys, Mohajerin Esfahani & Kuhn, From Data to Decisions: Distributionally Robust Optimization is Optimal, arXiv:1704.04118v3, pp. 8–11 (§2.2, (5), strong optimality), p. 14 (Definition 6, (10)), pp. 23–24 (§5, empirical distribution, Definition 8), pp. 29, 35 (γ̄, Ξ⋆)

import Mathlib

namespace DROOptimal.Continuous

open MeasureTheory Filter
open scoped ENNReal NNReal

/-- The model class 𝒫 of §5 (p. 23): all Borel probability distributions on the compact set
`Ξ ⊆ ℝ^d`, realized as `ProbabilityMeasure ↥Ξ` (Borel σ-algebra of the subtype). It carries Mathlib's
topology of weak convergence of probability measures, as §5 requires. -/
abbrev Dist {d : ℕ} (Ξ : Set (EuclideanSpace ℝ (Fin d))) : Type :=
  ProbabilityMeasure ↥Ξ

variable {d n : ℕ} {Ξ : Set (EuclideanSpace ℝ (Fin d))} {X : Set (EuclideanSpace ℝ (Fin n))}

/-- The model-based predictor `c(x, ℙ) = ∫_Ξ γ(x, ξ) dℙ(ξ)` (§5, p. 23). -/
noncomputable def cost (γ : ↥X → ↥Ξ → ℝ) (x : ↥X) (ℙ : Dist Ξ) : ℝ :=
  ∫ ξ, γ x ξ ∂(ℙ : Measure ↥Ξ)

/-- The generalized relative entropy `I(ℙ′, ℙ)` of Definition 8 (p. 24), as Mathlib's
Kullback–Leibler divergence `klDiv ℙ′ ℙ : ℝ≥0∞`. It is `∞` unless `ℙ′ ≪ ℙ`; for `ℙ′ ≪ ℙ` it is
`∫ log (dℙ′/dℙ) dℙ′` when this log-likelihood ratio is `ℙ′`-integrable and `∞` otherwise (the
integral then diverges to `+∞`, its negative part being always integrable). -/
noncomputable def relEnt (ℙ' ℙ : Dist Ξ) : ℝ≥0∞ :=
  InformationTheory.klDiv (ℙ' : Measure ↥Ξ) (ℙ : Measure ↥Ξ)

/-- The measure `(1/T) Σ_{t=1}^T δ_{ξ_t}` of a sample path `ω = (ξ_1, …, ξ_T)` (§5, p. 23). -/
noncomputable def empiricalMeasure {T : ℕ} (ω : Fin T → ↥Ξ) : Measure ↥Ξ :=
  (T : ℝ≥0∞)⁻¹ • ∑ t, Measure.dirac (ω t)

/-- The empirical distribution `ℙ̂_T = (1/T) Σ_t δ_{ξ_t}` (§5, p. 23), a probability measure for
`T ≥ 1`. -/
noncomputable def empirical {T : ℕ} (ω : Fin T → ↥Ξ) (hT : 0 < T) : Dist Ξ :=
  ⟨empiricalMeasure ω, ⟨by
    simp only [empiricalMeasure, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
      measure_univ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
      smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by exact_mod_cast hT.ne') (ENNReal.natCast_ne_top T)⟩⟩

/-- `ℙ^∞(ℙ̂_T satisfies E)`: the probability, when `ξ_1, …, ξ_T` are drawn independently from `ℙ`,
that the empirical distribution has property `E`. It is the (outer) measure of the set of sample
paths under the product measure `ℙ^T`. At `T = 0` it is the junk value `0`; every statement using it
is asymptotic in `T`. -/
noncomputable def sampleProb (ℙ : Dist Ξ) (T : ℕ) (E : Dist Ξ → Prop) : ℝ≥0∞ :=
  if hT : 0 < T then
    Measure.pi (fun _ : Fin T => (ℙ : Measure ↥Ξ)) {ω | E (empirical ω hT)}
  else 0

/-- `limsup_{T→∞} (1/T) log p_T ≤ −s` (with `log 0 = −∞`), for `s ∈ [0, ∞]`: for every finite
`r′ < s`, eventually `p_T ≤ e^{−r′ T}`. -/
def DecaysAtRate (s : ℝ≥0∞) (p : ℕ → ℝ≥0∞) : Prop :=
  ∀ r' : ℝ≥0, (r' : ℝ≥0∞) < s →
    ∀ᶠ T : ℕ in atTop, p T ≤ ENNReal.ofReal (Real.exp (-((r' : ℝ) * (T : ℝ))))

/-- `liminf_{T→∞} (1/T) log p_T ≥ −s` (with `log 0 = −∞`), for `s ∈ [0, ∞]`: for every finite
`s′ > s`, eventually `e^{−s′ T} ≤ p_T`. Vacuous when `s = ∞`. -/
def DecaysAtMostAtRate (s : ℝ≥0∞) (p : ℕ → ℝ≥0∞) : Prop :=
  ∀ s' : ℝ≥0, s < (s' : ℝ≥0∞) →
    ∀ᶠ T : ℕ in atTop, ENNReal.ofReal (Real.exp (-((s' : ℝ) * (T : ℝ)))) ≤ p T

/-- Data-driven predictors (the class 𝒞, p. 10, with Definition 3 read in §5): `ĉ : X × 𝒫 → ℝ`
continuous for the product of the Euclidean topology on `X` and the weak topology on 𝒫. -/
def IsPredictor (ĉ : ↥X → Dist Ξ → ℝ) : Prop :=
  Continuous (fun q : ↥X × Dist Ξ => ĉ q.1 q.2)

/-- Feasibility in the meta-optimization problem (5) (p. 10): `ĉ ∈ 𝒞` and, for all `x ∈ X` and
`ℙ ∈ 𝒫`, the out-of-sample disappointment `ℙ^∞(c(x, ℙ) > ĉ(x, ℙ̂_T))` satisfies
`limsup_T (1/T) log ℙ^∞(…) ≤ −r`. -/
def Feasible5 (γ : ↥X → ↥Ξ → ℝ) (r : ℝ) (ĉ : ↥X → Dist Ξ → ℝ) : Prop :=
  IsPredictor ĉ ∧
    ∀ (x : ↥X) (ℙ : Dist Ξ),
      DecaysAtRate (ENNReal.ofReal r) (fun T => sampleProb ℙ T (fun ℙ' => ĉ x ℙ' < cost γ x ℙ))

/-- Strong optimality in (5) (pp. 10–11): `ĉ` is feasible and `ĉ ⪯_𝒞 ĉ′`, i.e.
`ĉ(x, ℙ′) ≤ ĉ′(x, ℙ′)` for all `x, ℙ′`, for every feasible `ĉ′`. -/
def StronglyOptimal5 (γ : ↥X → ↥Ξ → ℝ) (r : ℝ) (ĉ : ↥X → Dist Ξ → ℝ) : Prop :=
  Feasible5 γ r ĉ ∧
    ∀ ĉ' : ↥X → Dist Ξ → ℝ, Feasible5 γ r ĉ' → ∀ (x : ↥X) (ℙ' : Dist Ξ), ĉ x ℙ' ≤ ĉ' x ℙ'

/-- The distributionally robust predictor `ĉ_r(x, ℙ′) = sup_{ℙ ∈ 𝒫} {c(x, ℙ) : I(ℙ′, ℙ) ≤ r}`
(Definition 6, (10), p. 14, constructed with Definition 8 as on p. 24). For `r ≥ 0` the set contains
`c(x, ℙ′)` and, for continuous `γ` on compact `X × Ξ`, is bounded above, so `sSup` is the supremum. -/
noncomputable def drPredictor (γ : ↥X → ↥Ξ → ℝ) (r : ℝ) (x : ↥X) (ℙ' : Dist Ξ) : ℝ :=
  sSup (cost γ x '' {ℙ : Dist Ξ | relEnt ℙ' ℙ ≤ ENNReal.ofReal r})

/-- The worst-case cost `γ̄(x) = max_{ξ ∈ Ξ} γ(x, ξ)` (pp. 24, 29), as a real supremum; for compact
nonempty `Ξ` and continuous `γ(x, ·)` it is attained. -/
noncomputable def worstCost (γ : ↥X → ↥Ξ → ℝ) (x : ↥X) : ℝ :=
  ⨆ ξ : ↥Ξ, γ x ξ

/-- The set of worst-case scenarios `Ξ⋆(x) = arg max_{ξ ∈ Ξ} γ(x, ξ)` (pp. 29, 35). -/
def worstSet (γ : ↥X → ↥Ξ → ℝ) (x : ↥X) : Set ↥Ξ :=
  {ξ | γ x ξ = worstCost γ x}

end DROOptimal.Continuous


