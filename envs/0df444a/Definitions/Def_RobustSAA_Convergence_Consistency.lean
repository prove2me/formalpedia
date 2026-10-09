-- Prove2me | Definitions.Def_RobustSAA_Convergence_Consistency
-- name    : RobustSAA_Convergence_Consistency
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T14:17:39.855667+00:00
-- url     : https://prove2.me/theorems/ca55d3e9-9ca6-403a-a134-5a605c68ebe2
-- title:
--   Definitions 2, 4, 5 — consistency, c-convergence, c-consistency of a GoF test; the empirical distribution
-- statement:
--   This file defines the companion consistency notions of §4.1, in the setting of `RobustSAA.Convergence.Setting` (a DUS map $N\mapsto\mathcal F_N$ on a closed support $\Xi\subseteq\mathbb R^d$, data $\xi^1,\xi^2,\dots$ i.i.d. from $F$).
--
--   1. **Consistency (Definition 2).** A test is consistent if, for every data-generating $F$ and every $F_0\neq F$,
--   $$\lim_{N\to\infty}\mathbb P\big(F_0\notin\mathcal F_N\big)=1 .$$
--   2. **$c$-convergence (Definition 4).** Given a cost $c(x;\xi)$ and a decision set $X$, a sequence $F_N$ $c$-converges to $F$ if $\mathbb E_{F_N}[c(x;\xi)]\to\mathbb E_F[c(x;\xi)]$ for all $x\in X$.
--   3. **$c$-consistency (Definition 5).** A test is $c$-consistent if, for every data-generating $F$, almost surely every sequence $F_N$ that does not $c$-converge to $F$ is rejected infinitely often:
--   $$\mathbb P\big(F_N\text{ does not }c\text{-converge to }F\implies F_N\notin\mathcal F_N\ \text{i.o.}\big)=1 .$$
--   4. **Empirical distribution.** $\hat F_N=\frac1N\sum_{i=1}^N\delta_{\xi^i}$.
--
--   Consistency is the classical property that uniform consistency strengthens (Proposition 4); $c$-consistency is the cost-specific relaxation under which Theorem 3 still gives convergence of Robust SAA.
--
--   **Formalization Note** Expectations are the extended-real `expect` of the setting file: $+\infty$ for a non-integrable integrand, on both sides of Definition 4. $\mathbb P(F_0\notin\mathcal F_N)$ is the product law evaluated at the event (an outer measure if the event is not measurable). The empirical distribution is given as a measure; Theorem 3 asks that some member of $\mathcal F_N$ equal it.
-- source:
--   Bertsimas, Gupta, Kallus, Robust Sample Average Approximation, arXiv:1408.4445v3, Definition 2 p. 12, Definitions 4–5 p. 14

import Mathlib
import Definitions.Def_RobustSAA_Convergence_Setting

open MeasureTheory Filter Topology
open scoped ENNReal

namespace RobustSAA.Convergence

variable {d : ℕ} {Ξ : Set (Pt d)}

/-- Definition 2 (p. 12): the test with confidence regions `𝓕` is consistent if, for every
data-generating `F` and every `F₀ ≠ F`, `ℙ(F₀ ∉ 𝓕_N) → 1` as `N → ∞`. -/
def IsConsistent (𝓕 : DUS Ξ) : Prop :=
  ∀ F F₀ : ProbabilityMeasure ↥Ξ, F₀ ≠ F →
    Tendsto (fun N => dataLaw F {ω | F₀ ∉ 𝓕 N (sample ω N)}) atTop (𝓝 1)

/-- Definition 4 (p. 14): given the cost `c`, the sequence `G N` `c`-converges to `F` if
`E_{G_N}[c(x; ξ)] → E_F[c(x; ξ)]` for all `x ∈ X`. -/
def CConverges {dx : ℕ} (X : Set (Pt dx)) (c : Pt dx → ↥Ξ → ℝ)
    (G : ℕ → ProbabilityMeasure ↥Ξ) (F : ProbabilityMeasure ↥Ξ) : Prop :=
  ∀ x ∈ X, Tendsto (fun N => expect (G N) (c x)) atTop (𝓝 (expect F (c x)))

/-- Definition 5 (p. 14): the test with confidence regions `𝓕` is `c`-consistent if, for every
data-generating `F`, almost surely, every sequence `F_N` that does not `c`-converge to `F` is
rejected infinitely often. -/
def IsCConsistent {dx : ℕ} (X : Set (Pt dx)) (c : Pt dx → ↥Ξ → ℝ) (𝓕 : DUS Ξ) : Prop :=
  ∀ F : ProbabilityMeasure ↥Ξ, ∀ᵐ ω ∂(dataLaw F), ∀ G : ℕ → ProbabilityMeasure ↥Ξ,
    ¬ CConverges X c G F → ∃ᶠ N in atTop, G N ∉ 𝓕 N (sample ω N)

/-- The empirical distribution `F̂_N = (1/N) ∑_{i=1}^N δ_{ξⁱ}` of a sample (as a measure). -/
noncomputable def empiricalMeasure {N : ℕ} (s : Fin N → ↥Ξ) : Measure ↥Ξ :=
  (N : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (s i)

end RobustSAA.Convergence


