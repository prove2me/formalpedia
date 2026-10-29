-- Prove2me | Definitions.Def_BramsonQueueing_Fluid_Renewal
-- name    : BramsonQueueing_Fluid_Renewal
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:18:18.047124+00:00
-- url     : https://prove2.me/theorems/a66fbc92-a745-43e8-a669-4f2798522959
-- title:
--   Positive iid increments and the pending-renewal count and maximum
-- statement:
--   Let $\beta_0,\beta_1,\ldots$ be measurable, independent identically distributed nonnegative random variables that are strictly positive almost surely and have finite mean $m$. Write $S_n=\sum_{i<n}\beta_i$ and let $G_\beta$ be the event $S_n/n\to m$. The source numbers these increments starting at one. The two scaled pending-renewal quantities are
--   $$B_1(t)=\frac{\sup\{n+1:S_n\le t\}}{t},\qquad B_2(t)=\frac{\sup\{\beta_n:S_n\le t\}}{t}.$$
--   Both include the first pending increment, even if that increment ends after $t$. Extended nonnegative suprema retain infinite values on exceptional paths. The uniform-tail predicate asserts that for every positive tolerance, every sufficiently large threshold bounds all tail expectations in the family by that tolerance. No second moment, boundedness, or density is assumed. Division at zero is total in Lean, but no target uses a finite-time assertion for these ratios at zero.
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), https://doi.org/10.1007/978-3-540-68896-9; published edition; Lemma 4.13 setup, printed 116 / PDF 124, equations (4.81)–(4.83).

import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace BramsonQueueing.Fluid

/-- Positive iid finite-mean increments; indices zero, one, ... encode the
source's indices one, two, ... . No higher moment or density assumption. -/
structure PositiveIID (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) where
  beta : ℕ → Ω → ℝ≥0
  measurable : ∀ n, Measurable (beta n)
  positive : ∀ n, ∀ᵐ ω ∂μ, 0 < beta n ω
  independent : iIndepFun beta μ
  identically_distributed : ∀ n, IdentDistrib (beta n) (beta 0) μ μ
  finite_mean : Integrable (fun ω => (beta 0 ω : ℝ)) μ

noncomputable def renewalMean {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (r : PositiveIID Ω μ) : ℝ := ∫ ω, (r.beta 0 ω : ℝ) ∂μ

noncomputable def renewalSum {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (r : PositiveIID Ω μ) (n : ℕ) (ω : Ω) : ℝ≥0 := ∑ i ∈ Finset.range n, r.beta i ω

def RenewalGood {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (r : PositiveIID Ω μ) (ω : Ω) : Prop :=
  Tendsto (fun n : ℕ => (renewalSum r n ω : ℝ) / n) atTop (𝓝 (renewalMean r))

/-- The count includes the first pending increment. Infinite exceptional counts
are retained, rather than a natural or real supremum's default value. -/
noncomputable def renewalB1 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (r : PositiveIID Ω μ) (t : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  (⨆ n : ℕ, ⨆ (_ : renewalSum r n ω ≤ t), ((n + 1 : ℕ) : ℝ≥0∞)) / t

noncomputable def renewalB2 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (r : PositiveIID Ω μ) (t : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  (⨆ n : ℕ, ⨆ (_ : renewalSum r n ω ≤ t), (r.beta n ω : ℝ≥0∞)) / t

/-- Uniform tail expectation tending to zero, written without a real supremum. -/
def UniformTail {I Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F : I → Ω → ℝ≥0∞) : Prop :=
  ∀ ε : ℝ≥0, 0 < ε → ∃ M₀ : ℝ≥0, ∀ M ≥ M₀, ∀ i,
    (∫⁻ ω in {ω | (M : ℝ≥0∞) ≤ F i ω}, F i ω ∂μ) ≤ ε

end BramsonQueueing.Fluid


