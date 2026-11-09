-- Prove2me | Definitions.Def_PagingDelay_PMD_Rounding
-- name    : PagingDelay_PMD_Rounding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:24.999406+00:00
-- url     : https://prove2.me/theorems/9818240b-a1a7-44dc-8022-04699fe35122
-- title:
--   Online rounding interface for arbitrary fractional cache prefixes
-- statement:
--   A fractional cache is a vector $y\in[0,1]^n$ with $\sum_i y_i=k$. A valid history is a nonempty finite list of such vectors beginning at the indicator of the fixed initial cache $O_0$.
--
--   An online rounding map is a probability space together with a map from a seed and a finite history to a cache set; its value therefore cannot see later vectors. Membership events for each history and page are measurable. Its marginals and the expected fetch cost of extending a history by one vector are the corresponding probabilities and nonnegative integrals.
--
--   $$\mathbb E\!\left[\sum_{i\in R(y^{(0)},\ldots,y^{(\nu+1)})\setminus R(y^{(0)},\ldots,y^{(\nu)})}w_i\right].$$
--
--   The interface assumes no cache cardinality, initial cache, exact marginal or movement bound. Corollary 33 asserts all of those properties.
-- source:
--   Julian Born, Yann Disser, Linda Thelen, Tight weighted paging with delay via mirror descent, STOC 2027 submission #453 (October 2026), Corollary 33, p. 26. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/453.pdf

import Definitions.Def_PagingDelay_PMD_Path

noncomputable section

namespace PagingDelay.PMD
open MeasureTheory
open scoped BigOperators Classical

/-- Only the probabilistic data and prefix interface; no marginals or bound are assumed. -/
structure OnlineRounding (n : ℕ) where
  Seed : Type
  measurableSpace : MeasurableSpace Seed
  law : @Measure Seed measurableSpace
  probability : @IsProbabilityMeasure Seed measurableSpace law
  choose : Seed → List (Fin n → ℝ) → Finset (Fin n)
  measurable : ∀ ys i,
    letI := measurableSpace
    MeasurableSet {ω | i ∈ choose ω ys}

def FractionalCache {n : ℕ} (k : ℕ) (y : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ ∑ i, y i = k

def indicator {n : ℕ} (O₀ : Finset (Fin n)) (i : Fin n) : ℝ := if i ∈ O₀ then 1 else 0

def CacheHistory {n : ℕ} (k : ℕ) (O₀ : Finset (Fin n)) (ys : List (Fin n → ℝ)) : Prop :=
  ys.head? = some (indicator O₀) ∧ ∀ y ∈ ys, FractionalCache k y

def roundingMarginal {n : ℕ} (R : OnlineRounding n) (ys : List (Fin n → ℝ)) (i : Fin n) : ENNReal :=
  letI := R.measurableSpace
  R.law {ω | i ∈ R.choose ω ys}

def roundingFetch {n : ℕ} (w : Fin n → ℝ) (R : OnlineRounding n)
    (ys : List (Fin n → ℝ)) (y : Fin n → ℝ) : ENNReal :=
  letI := R.measurableSpace
  MeasureTheory.lintegral R.law (fun ω =>
    ∑ i ∈ R.choose ω (ys ++ [y]) \ R.choose ω ys, ENNReal.ofReal (w i))

end PagingDelay.PMD


