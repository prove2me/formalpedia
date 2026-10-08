-- Prove2me | Definitions.Def_DupacovaWets_Consistency_Assumptions
-- name    : DupacovaWets_Consistency_Assumptions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T13:47:10.416312+00:00
-- url     : https://prove2.me/theorems/70a3cf00-c25e-4db3-b1ed-0185119022a0
-- title:
--   Assumption 3.4 (continuities of $f$) and Assumption 3.5 (convergence in distribution)
-- statement:
--   Let $\Xi$ be a topological space carrying a $\sigma$-field, $f:\mathbb R^n\times\Xi\to[-\infty,\infty]$ and $S\subseteq\mathbb R^n$.
--
--   **Assumption 3.4** holds when:
--   1. $f$ takes values in $(-\infty,\infty]$ and $\operatorname{dom} f=\{(x,\xi): f(x,\xi)<\infty\}=S\times\Xi$ with $S$ closed and nonempty;
--   2. for every $x\in S$, $\xi\mapsto f(x,\xi)$ is continuous on $\Xi$;
--   3. for every $\xi$, $x\mapsto f(x,\xi)$ is lower semicontinuous on $\mathbb R^n$;
--   4. $f$ is locally lower Lipschitz on $S$: each $x\in S$ has a neighbourhood $V$ and a bounded continuous $\beta:\Xi\to\mathbb R$ with
--
--   $$
--   f(x,\xi)-f(x',\xi)\le\beta(\xi)\,\|x-x'\| \qquad\text{for all } x'\in V\cap S,\ \xi\in\Xi. \tag{3.10}
--   $$
--
--   Let further $P$ be a measure on $\Xi$, $(Z,\mathcal F,\mu)$ a measure space with an increasing sequence of sub-$\sigma$-fields $\mathcal F^1\subseteq\mathcal F^2\subseteq\cdots\subseteq\mathcal F$, and $P^\nu(\cdot,\zeta)$, $\nu\ge1$, measures on $\Xi$. **Assumption 3.5** holds when:
--   1. each $P^\nu(\cdot,\zeta)$ is a probability measure, and $\zeta\mapsto P^\nu(A,\zeta)$ is $\mathcal F^\nu$-measurable for every measurable $A\subseteq\Xi$;
--   2. for $\mu$-almost every $\zeta$: $P^\nu(\cdot,\zeta)$ converges in distribution to $P$, i.e. $\int g\,dP^\nu(\cdot,\zeta)\to\int g\,dP$ for every bounded continuous $g$; with $P^0=P$, for every $x\in S$ and $\varepsilon>0$ there is a compact $K_\varepsilon\subseteq\Xi$ with
--
--   $$
--   \int_{\Xi\setminus K_\varepsilon}|f(x,\xi)|\,P^\nu(d\xi,\zeta)<\varepsilon\quad(\nu=0,1,\dots) \tag{3.11}
--   $$
--
--   and
--
--   $$
--   \int_\Xi \inf_{x\in\mathbb R^n} f(x,\xi)\,P^\nu(d\xi,\zeta)>-\infty\quad(\nu=0,1,\dots). \tag{3.12}
--   $$
--
--   These are the two hypotheses under which all results of §3 of Dupačová and Wets are proved: (3.11) is a uniform-integrability (asymptotic negligibility) condition and (3.12) asks that the infimal function be quasi-integrable.
--
--   **Formalization Note** (3.10) is written additively, $f(x,\xi)\le f(x',\xi)+\beta(\xi)\|x-x'\|$, which is equivalent because both values are finite for $x,x'\in S$; the norm is the Euclidean one (any norm works, $\beta$ being arbitrary). Lean's `Pν k`, `𝔽 k` are the paper's $P^{k+1}$, $\mathcal F^{k+1}$. One null set serves all $x\in S$ in (3.11) and $K_\varepsilon$ is uniform in $\nu$, as printed. The integrals in (3.11) are Lebesgue integrals of $|f(x,\cdot)|$ (finite on $S$); the integral in (3.12) is the expectation `expect` with the convention of p. 10. That $P$ and $\mu$ are probability measures is stated in the theorems that use these assumptions.
-- source:
--   Dupačová & Wets, IIASA Working Paper WP-86-41 (Aug. 1986), p. 15, Assumption 3.4 (incl. (3.10)); pp. 15–16, Assumption 3.5 (incl. (3.11), (3.12))

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
open MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace DupacovaWets.Consistency

/-- Dupačová–Wets (WP-86-41), p. 15, Assumption 3.4 ("Continuities" of `f`):
`f : ℝⁿ × Ξ → (-∞, ∞]` with `dom f = S × Ξ`, `S` closed and nonempty; `ξ ↦ f(x, ξ)` continuous
for `x ∈ S`; `x ↦ f(x, ξ)` lower semicontinuous on `ℝⁿ` for every `ξ`; and locally lower
Lipschitz on `S`: each `x ∈ S` has a neighbourhood `V` and a bounded continuous `β : Ξ → ℝ`
with `f(x, ξ) - f(x', ξ) ≤ β(ξ) ‖x - x'‖` for `x' ∈ V ∩ S` (3.10), written additively. -/
structure Assumption3_4 {n : ℕ} {Ξ : Type*} [TopologicalSpace Ξ]
    (f : EuclideanSpace ℝ (Fin n) → Ξ → EReal) (S : Set (EuclideanSpace ℝ (Fin n))) : Prop where
  isClosed_S : IsClosed S
  nonempty_S : S.Nonempty
  ne_bot : ∀ x ξ, f x ξ ≠ ⊥
  lt_top_iff : ∀ x ξ, f x ξ < ⊤ ↔ x ∈ S
  continuous_of_mem : ∀ x ∈ S, Continuous (f x)
  lsc : ∀ ξ, LowerSemicontinuous (fun x => f x ξ)
  lowerLipschitz : ∀ x ∈ S, ∃ V ∈ 𝓝 x, ∃ β : Ξ →ᵇ ℝ, ∀ x' ∈ V ∩ S, ∀ ξ,
    f x ξ ≤ f x' ξ + ((β ξ * ‖x - x'‖ : ℝ) : EReal)

/-- Pp. 15–16, Assumption 3.5 (convergence in distribution). `Pν k ζ` is the paper's
`P^{k+1}(·, ζ)` and `𝔽 k` its `F^{k+1}`; `P = P⁰(·, ζ)` is kept separate. Every `P^ν(·, ζ)` is a
probability measure, `ζ ↦ P^ν(A, ζ)` is `F^ν`-measurable for every measurable `A`, and for
`μ`-almost every `ζ`: `P^ν(·, ζ)` converges in distribution to `P`; for every `x ∈ S` and
`ε > 0` one compact `K_ε` satisfies `∫_{Ξ \ K_ε} |f(x, ξ)| P^ν(dξ, ζ) < ε` for `ν = 0, 1, …`
(3.11); and `∫ inf_x f(x, ξ) P^ν(dξ, ζ) > -∞` for `ν = 0, 1, …` (3.12). -/
structure Assumption3_5 {n : ℕ} {Ξ : Type*} [TopologicalSpace Ξ] [MeasurableSpace Ξ]
    {Z : Type*} [mZ : MeasurableSpace Z]
    (f : EuclideanSpace ℝ (Fin n) → Ξ → EReal) (S : Set (EuclideanSpace ℝ (Fin n)))
    (P : Measure Ξ) (μ : Measure Z) (𝔽 : Filtration ℕ mZ) (Pν : ℕ → Z → Measure Ξ) : Prop where
  isProb : ∀ k ζ, IsProbabilityMeasure (Pν k ζ)
  adapted : ∀ k (A : Set Ξ), MeasurableSet A → Measurable[𝔽 k] (fun ζ => Pν k ζ A)
  ae : ∀ᵐ ζ ∂μ,
    (∀ g : Ξ →ᵇ ℝ, Tendsto (fun k => ∫ ξ, g ξ ∂(Pν k ζ)) atTop (𝓝 (∫ ξ, g ξ ∂P))) ∧
    (∀ x ∈ S, ∀ ε : ℝ, 0 < ε → ∃ K : Set Ξ, IsCompact K ∧
      ∫⁻ ξ in Kᶜ, ENNReal.ofReal |(f x ξ).toReal| ∂P < ENNReal.ofReal ε ∧
      ∀ k, ∫⁻ ξ in Kᶜ, ENNReal.ofReal |(f x ξ).toReal| ∂(Pν k ζ) < ENNReal.ofReal ε) ∧
    (⊥ < expect P (fun ξ => ⨅ x, f x ξ) ∧ ∀ k, ⊥ < expect (Pν k ζ) (fun ξ => ⨅ x, f x ξ))

end DupacovaWets.Consistency


