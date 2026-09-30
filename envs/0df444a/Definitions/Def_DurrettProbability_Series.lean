-- Prove2me | Definitions.Def_DurrettProbability_Series
-- name    : DurrettProbability_Series
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-18T17:01:56.577934+00:00
-- url     : https://prove2.me/theorems/0cd2ebc7-6a84-4ab4-b86e-841205bed86d
-- title:
--   Convergence of random series, truncation, and the exchangeable sigma-field
-- statement:
--   Four notions from section 2.5 of Durrett, *Probability: Theory and Examples*.
--
--   **Partial sums.** For a sequence $X_1,X_2,\dots$ of random variables, $S_N = \sum_{n<N}X_n$.
--
--   **Almost sure convergence of a series.** The series $\sum_n X_n$ converges almost surely when for
--   almost every $\omega$ there is a real number $L$ with $S_N(\omega)\to L$. Following Durrett, "the
--   series converges" means the partial sums have a limit, *not* that the series converges absolutely.
--
--   **Truncation.** For a level $A>0$, the truncation of $X$ is
--   $$Y = X\,\mathbb{1}(|X|\le A),$$
--   the variable that agrees with $X$ where $|X|\le A$ and vanishes elsewhere. It is bounded, so its
--   mean and variance always exist — which is why Kolmogorov's three-series theorem can dispense with
--   any integrability assumption on $X$ itself.
--
--   **Permutable events.** A *finite permutation* of $\mathbb{N}$ is a bijection fixing all but
--   finitely many indices. An event $A$ in a sequence space is **permutable**, or exchangeable, when
--   rearranging finitely many coordinates leaves it unchanged: $\{\omega : \omega\circ\sigma\in A\}=A$
--   for every finite permutation $\sigma$. Examples are $\{S_n\in B \text{ infinitely often}\}$ and
--   $\{\limsup_n S_n/c_n\ge1\}$, since permuting finitely many coordinates does not change $S_n$ for
--   large $n$; every tail event is permutable, and the first example shows the converse fails. The
--   permutable events form the exchangeable σ-field $\mathcal{E}$.
--
--   **Formalization Note** Convergence of a series is the convergence of the sequence of partial sums
--   to a real limit, not Mathlib's `Summable`, which for real series means unconditional and hence
--   absolute convergence. The distinction matters in condition (ii) of the three-series theorem.
--   Almost sure convergence asserts the existence of a limit for almost every outcome without claiming
--   the limit is a measurable function. A permutable event is defined directly by its invariance
--   property rather than by constructing the exchangeable σ-field as an object.
-- source:
--   Durrett, Probability: Theory and Examples, Version 5 (11 January 2019), section 2.5, pp. 82-85 (PDF pp. 90-93): the exchangeable sigma-field and permutable events p. 82, the convention that 'sum a_n converges' means lim_N sum_{n<=N} a_n exists p. 84, and the truncation Y_i = X_i 1(|X_i| <= A) of Theorem 2.5.8 p. 85. sha256 aeac36cbf5e44c53d69fa60a2d29a393e2d0e8c955ee103bd845d925fd910886

import Mathlib

open MeasureTheory ProbabilityTheory Filter

namespace DurrettProbability

/-- The partial sums `S_n = X_1 + ⋯ + X_n` of a sequence of random variables. -/
def partialSum {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ := ∑ i ∈ Finset.range n, X i ω

/-- The series `∑ X_n` **converges almost surely**: for almost every `ω` the partial sums
`S_N(ω)` converge to some real limit.  Durrett, *Probability: Theory and Examples*, section 2.5. -/
def SeriesConvergesAE {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∀ᵐ ω ∂μ, ∃ L : ℝ, Tendsto (fun N => partialSum X N ω) atTop (nhds L)

/-- The truncation `Y = X · 1(|X| ≤ A)` used in Kolmogorov's three-series theorem. -/
noncomputable def truncate {Ω : Type*} (A : ℝ) (X : Ω → ℝ) : Ω → ℝ := fun ω => if |X ω| ≤ A then X ω else 0

/-- A **finite permutation** of `ℕ`: a bijection moving only finitely many indices. -/
def FinitelySupported (σ : Equiv.Perm ℕ) : Prop := ∀ᶠ i in Filter.cofinite, σ i = i

/-- A **permutable** (exchangeable) event: a measurable set of sequences whose occurrence is
unaffected by rearranging finitely many coordinates.  These form the exchangeable σ-field `ℰ` of
Durrett, section 2.5. -/
def IsPermutable {S : Type*} [MeasurableSpace S] (A : Set (ℕ → S)) : Prop :=
  MeasurableSet A ∧ ∀ σ : Equiv.Perm ℕ, FinitelySupported σ → (fun ω => ω ∘ σ) ⁻¹' A = A

end DurrettProbability


