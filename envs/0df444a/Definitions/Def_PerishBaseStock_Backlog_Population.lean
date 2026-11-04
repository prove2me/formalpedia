-- Prove2me | Definitions.Def_PerishBaseStock_Backlog_Population
-- name    : PerishBaseStock_Backlog_Population
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T02:43:08.933316+00:00
-- url     : https://prove2.me/theorems/a77713f4-cdb5-4cef-b6c3-6e2c10262dec
-- title:
--   Demand-population form (7) of the one-period demand
-- statement:
--   Fix a positive integer $n$, the **demand population size**. Let $\hat D_1,\hat D_2,\dots$ be i.i.d. nonnegative random variables with finite mean and variance and $\mathbb E[\hat D_1]>0$, and, independently, let $X_1,X_2,\dots$ be i.i.d. nonnegative random variables with $\mathbb E[X_1]=1$, finite variance, and $\mathbb E[e^{sX_1}]<\infty$ for some $s>0$. Set
--
--   $$N(n)=\sup\Big\{N\in\mathbb N:\ \sum_{k=1}^{N}\frac{X_k}{n}\le1\Big\},\qquad D(n)=\sum_{j=1}^{N(n)}\hat D_j .$$
--
--   $N(n)$ is the number of renewals in one unit of time of a renewal process with inter-arrival times $X_k/n$, and $D(n)$ is the total demand of a period in which $N(n)$ customers each request $\hat D_j$ units. The definition provides the law of $D(n)$, the generic one-period demand of the regime "large demand population".
--
--   **Formalization Note** $N(n)$ takes values in $\mathbb N\cup\{\infty\}$; on the null event where the sum defining $D(n)$ is infinite, $D(n)$ is set to $0$, which does not change its law. The positivity $\mathbb E[\hat D_1]>0$ is the model's standing $\mathbb E[D]>0$.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. 11, eq. (7) and the assumptions stated after it (used by Theorem 2, p. 12, and Theorem 7(b), p. 20)

import Definitions.Def_CappedBaseStock_Model
import Definitions.Def_PerishBaseStock_Population_CompoundDemand

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

namespace PerishBaseStock.Backlog

/-! # The demand-population form (7) (Bu, Gong & Chao, p. 11)

`D = Σ_{j=1}^{N(n)} D̂_j` with `N(n) = sup{N ∈ ℕ : Σ_{k=1}^N X_k / n ≤ 1}`. Indices are
zero-based: `ω.1 j` is `D̂_{j+1}` and `ω.2 k` is `X_{k+1}`. -/

/-- The data of (7) and the assumptions of Theorem 2: the laws of `D̂₁` and of `X₁`.
`D̂₁` is non-negative with finite mean and variance, and `E[D̂₁] > 0` (implicit in the
model's `E[D] > 0`, p. 8); `X₁` is non-negative with mean one, finite variance, and
`E[e^{s X₁}] < ∞` for some `s > 0`. -/
structure PopulationModel where
  lawHat : Measure ℝ≥0
  lawX : Measure ℝ≥0
  probHat : IsProbabilityMeasure lawHat
  probX : IsProbabilityMeasure lawX
  hatMean : Integrable (fun y : ℝ≥0 => (y : ℝ)) lawHat
  hatVar : Integrable (fun y : ℝ≥0 => (y : ℝ) ^ 2) lawHat
  hatMeanPos : 0 < ∫ y : ℝ≥0, (y : ℝ) ∂lawHat
  xIntegrable : Integrable (fun y : ℝ≥0 => (y : ℝ)) lawX
  xMeanOne : ∫ y : ℝ≥0, (y : ℝ) ∂lawX = 1
  xVar : Integrable (fun y : ℝ≥0 => (y : ℝ) ^ 2) lawX
  xExpMoment : ∃ s : ℝ, 0 < s ∧ Integrable (fun y : ℝ≥0 => Real.exp (s * y)) lawX

attribute [instance] PopulationModel.probHat PopulationModel.probX

/-- Two independent i.i.d. sequences, `D̂_j ∼ lawHat` and `X_k ∼ lawX`. -/
def popLaw (M : PopulationModel) : Measure PerishBaseStock.Population.PopSample :=
  (Measure.infinitePi fun _ : ℕ => M.lawHat).prod (Measure.infinitePi fun _ : ℕ => M.lawX)

/-- `N(n) = sup{N ∈ ℕ : Σ_{k=1}^N X_k / n ≤ 1}`, in `ℕ∞` (it is `⊤` on a null event). -/
def renewalCount (n : ℕ) (x : ℕ → ℝ≥0) : ℕ∞ :=
  ⨆ (N : ℕ) (_ : (∑ k ∈ Finset.range N, (x k : ℝ)) / n ≤ 1), (N : ℕ∞)

/-- The one-period demand `D(n) = Σ_{j=1}^{N(n)} D̂_j`: the term `D̂_{j+1}` is counted iff
`j + 1 ≤ N(n)`. On the null event where the sum is infinite the value is set to `0`. -/
def popDemand (n : ℕ) (ω : PerishBaseStock.Population.PopSample) : ℝ≥0 :=
  (∑' j : ℕ, if ((j + 1 : ℕ) : ℕ∞) ≤ renewalCount n ω.2 then (ω.1 j : ℝ≥0∞) else 0).toNNReal

/-- The law of the one-period demand `D(n)` of form (7). -/
def popDemandLaw (M : PopulationModel) (n : ℕ) : Measure ℝ≥0 :=
  Measure.map (popDemand n) (popLaw M)

end PerishBaseStock.Backlog


