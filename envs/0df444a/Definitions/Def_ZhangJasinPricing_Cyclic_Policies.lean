-- Prove2me | Definitions.Def_ZhangJasinPricing_Cyclic_Policies
-- name    : ZhangJasinPricing_Cyclic_Policies
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T06:57:27.319126+00:00
-- url     : https://prove2.me/theorems/490eda7c-9992-4902-9e4d-df6d244a3b13
-- title:
--   Cyclic policy classes, unrestricted benchmarks, and positive gaps
-- statement:
--   A word is a nonempty finite list of feasible price indices, repeated indefinitely. Its length is unrestricted. Decreasing words have nondecreasing indices because prices are strictly decreasing in their index. The threshold function uses one-based word positions and the sentinel price zero at position zero. Its maximum and empty fallback use the same strict comparison, as disclosed in finding I4. A threshold-regulated word obeys each threshold and has its minimum price last. Nested decreasing words are concatenations of nonempty decreasing segments agreeing on every common prefix position; they also carry the section's last-minimum convention. Segment indices range over the segments, resolving the printed M/S typo.
--
--   Expected empty-start cycle revenue is calculated directly from cohort means and operational demand, then divided by word length. Benchmarks are suprema over the full classes, not over a bounded DP search. These revenue sets are nonempty and bounded for every model: a singleton word is feasible and p₁(K+1) times the total cohort mean bounds every average. An optimal word attains this supremum. The set of positive gaps contains exactly strictly positive differences between this benchmark and average word revenue. No minimum, attainment, DP correctness, or short representative is assumed.
--
--   For the decreasing-policy length bound, decreasingCycleLength assigns one to any nonempty constant word, exactly as stipulated on p. 11; a nonstatic decreasing word has its full list length. No word is removed from the benchmark class.
-- source:
--   Zhang and Jasin (2021), DOI 10.1287/msom.2021.0979, supplied 34-page artifact, §§3–6, p. 15 (PDF p. 15)

import Definitions.Def_ZhangJasinPricing_Cyclic_Model
open MeasureTheory
open scoped BigOperators
open scoped Classical
noncomputable section

namespace ZhangJasinPricing.Cyclic
abbrev Word := List ℕ

def IsWord (M : ℕ) (w : Word) : Prop := w ≠ [] ∧ ∀ i ∈ w, i < M

def repeated (w : Word) (t : ℕ) : ℕ := w[t % w.length]?.getD 0

def Decreasing (M : ℕ) (w : Word) : Prop :=
  IsWord M w ∧ w.Pairwise (· ≤ ·)

/-- Page 11 assigns cycle length one to a static policy, even when its
word repeats the same price. A nonstatic decreasing word has its full word length. -/
def decreasingCycleLength (w : Word) : ℕ :=
  if w = [] then 0 else if w.Pairwise (· = ·) then 1 else w.length

/-- One-based word positions, with the threshold sentinel equal to zero. -/
def wordPrice (p : ℕ → ℝ) (w : Word) (t : ℕ) : ℝ :=
  if t = 0 then 0 else p (w[t-1]?.getD 0)

def threshold (p : ℕ → ℝ) (w : Word) (t : ℕ) : ℕ :=
  if wordPrice p w (t-1) < wordPrice p w t then t-1
  else ((Finset.Icc 1 (t-2)).filter (fun k =>
    wordPrice p w k < wordPrice p w (k+1) ∧
    wordPrice p w k < wordPrice p w (t-1))).sup id

def LastMinimum (w : Word) : Prop := ∀ i ∈ w, i ≤ w.getLastD 0

def ThresholdRegulated (M : ℕ) (p : ℕ → ℝ) (w : Word) : Prop :=
  IsWord M w ∧ LastMinimum w ∧
  ∀ t ∈ Finset.Icc 1 w.length, wordPrice p w (threshold p w t) ≤ wordPrice p w t

def NestedDecreasing (M : ℕ) (w : Word) : Prop :=
  IsWord M w ∧ LastMinimum w ∧ ∃ segments : List Word,
    segments.flatten = w ∧ (∀ s ∈ segments, Decreasing M s) ∧
    ∀ s ∈ segments, ∀ s' ∈ segments, ∀ j, j < min s.length s'.length → s[j]? = s'[j]?

/-- Expected empty-start cycle revenue by linearity in the time-stationary cohort means. -/
def cycleRevenue {Ω : Type} [MeasurableSpace Ω] (D : Model Ω) (w : Word) : ℝ :=
  ∑ t ∈ Finset.range w.length,
    D.price (repeated w t) * demand D (fun _ a k => D.mean a k) (repeated w) t

def averageRevenue {Ω : Type} [MeasurableSpace Ω] (D : Model Ω) (w : Word) : ℝ :=
  cycleRevenue D w / w.length

inductive Mode | decreasing | threshold deriving DecidableEq

def PolicyClass {Ω : Type} [MeasurableSpace Ω] (D : Model Ω) (mode : Mode) : Set Word :=
  match mode with
  | .decreasing => {w | Decreasing D.M w}
  | .threshold => {w | ThresholdRegulated D.M D.price w}

/-- The full, untruncated policy class. For admissible models the set is nonempty
and bounded above by p_1 (K+1) times the total cohort mean. -/
def benchmark {Ω : Type} [MeasurableSpace Ω] (D : Model Ω) (mode : Mode) : ℝ :=
  sSup (averageRevenue D '' PolicyClass D mode)

def Optimal {Ω : Type} [MeasurableSpace Ω] (D : Model Ω) (mode : Mode) (w : Word) : Prop :=
  w ∈ PolicyClass D mode ∧ averageRevenue D w = benchmark D mode

def positiveGaps {Ω : Type} [MeasurableSpace Ω] (D : Model Ω) (mode : Mode) : Set ℝ :=
  {d | 0 < d ∧ ∃ w ∈ PolicyClass D mode, d = benchmark D mode - averageRevenue D w}
end ZhangJasinPricing.Cyclic


