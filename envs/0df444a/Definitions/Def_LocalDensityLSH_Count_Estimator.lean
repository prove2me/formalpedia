-- Prove2me | Definitions.Def_LocalDensityLSH_Count_Estimator
-- name    : LocalDensityLSH_Count_Estimator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:22:02.342486+00:00
-- url     : https://prove2.me/theorems/440413fb-f42d-47cb-a32e-1f77ceb79570
-- title:
--   (2), §4–§5, App. B, pp. 6–15, 35 — the sampling pool, the weight Z, W, one LSH Count estimate, the median, and the joint law of tables and samples
-- statement:
--   This file defines the *LSH Count* estimator and the law of its randomness (Wu, Charikar and Natchu, (2) and §4–§5).
--
--   **Pool.** Given $K$ tables $\tau_1,\dots,\tau_K$, the sampling pool is the multiset of pairs $(k,x)$ with $x\in\mathcal B^k_q(\mathcal I)$, i.e. the union of the probed buckets of all tables, with a point that is probed in several tables appearing once per table. Its size is $\sum_{k=1}^K C^k_q(\mathcal I)$, where $C^k_q(\mathcal I)$ is the number of data points in the probed buckets of table $k$.
--
--   **Weight (2).** A sample $(k,x)$ receives the weight
--   $$Z=\begin{cases}\dfrac{\sum_{k=1}^K C^k_q(\mathcal I)}{K\cdot p(x)} & \text{if } x\in\mathcal A_q,\\[2mm] 0&\text{otherwise.}\end{cases}$$
--
--   **Table bias.** $W=\dfrac1K\sum_{k=1}^K\sum_{x\in\mathcal A_q}\dfrac{\mathbb 1(x\in\mathcal B^k_q(\mathcal I))}{p(x)}$.
--
--   **One estimate.** With $S$ samples and weights $Z_1,\dots,Z_S$ the estimator reports $\frac1S\sum_{i=1}^S Z_i$.
--
--   **Median.** Of $M$ estimates $E_1,\dots,E_M$ the final answer is their median, taken as the lower median: the entry of index $\lfloor (M-1)/2\rfloor$ (counting from $0$) of the sorted list.
--
--   **Sampler.** Given the tables, a sample is a uniformly random element of the pool. If the pool is empty, the sampler returns a uniform pair from all $K\cdot n$ pairs; every weight is $0$ in that case.
--
--   **One estimator run.** Tables $T_1,\dots,T_K$ and samples $X_1,\dots,X_S$ on a probability space $(\Omega,P)$ form a run when they are measurable and their joint law is
--   $$P\big(T_k=\tau_k\ \forall k,\ X_s=\xi_s\ \forall s\big)=\prod_{k=1}^K\mu(\{\tau_k\})\cdot\prod_{s=1}^S w_\tau(\xi_s),$$
--   where $w_\tau$ is the sampler's law given the tables. So the $K$ tables are independent with law $\mu$, and given the tables the $S$ samples are drawn independently, with replacement, from the pool.
--
--   **Median of means run.** $M$ estimator runs, each with its own tables and samples, form a run of the full estimator when they are mutually independent.
--
--   **Formalization Note.** Since $C=0$ on an empty pool, the formula for $Z$ already gives weight $0$ there, which is the convention the paper's Lemma 1 needs (the paper does not discuss the empty pool). The joint law is stated on atoms, which determines it because tables and samples take finitely many values. The sampler's weights are in `ℝ≥0∞`. The median uses `List.insertionSort` and returns $0$ for $M=0$.
-- source:
--   Wu, Charikar & Natchu, Local Density Estimation in High Dimensions, arXiv:1809.07471v1, (2) and the estimate Σ Z_i/S, p. 6; W, p. 9; sampler over the pooled buckets, §4.3, p. 13 and App. B, p. 35; sampling probabilities, proof of Lemma 1, p. 10; median of means, p. 15

import Mathlib
import Definitions.Def_LocalDensityLSH_Count_Model

namespace LocalDensityLSH.Count

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The sampling pool (§4.3, p. 13; App. B, p. 35): the multiset of pairs `(k, i)` such that, in
table `k`, the point `vᵢ` lies in a bucket at Hamming distance `ℐ` from the query. A point that
sits in the probed buckets of several tables appears once per table. -/
noncomputable def pool {n t K : ℕ} (I : Finset ℕ) (τs : Fin K → Table n t) :
    Finset (Fin K × Fin n) := by
  classical
  exact Finset.univ.filter (fun y => InBucket I (τs y.1) y.2)

/-- `Σ_{k=1}^K C^k_q(ℐ)`: the total size of the pool. -/
noncomputable def C {n t K : ℕ} (I : Finset ℕ) (τs : Fin K → Table n t) : ℕ :=
  (pool I τs).card

/-- The weight (2), p. 6, of a sample `y = (k, x)`:
`Z = Σ_k C^k_q(ℐ) / (K · p(x))` if `x ∈ 𝒜q`, and `0` otherwise. On an empty pool `C = 0`, so every
weight is `0` (the empty-pool convention). -/
noncomputable def Zval {n t K : ℕ} (μ : Measure (Table n t)) (I : Finset ℕ) (𝒜q : Finset (Fin n))
    (τs : Fin K → Table n t) (y : Fin K × Fin n) : ℝ :=
  if y.2 ∈ 𝒜q then (C I τs : ℝ) / ((K : ℝ) * p μ I y.2) else 0

/-- `W = (1/K) Σ_{k=1}^K Σ_{x ∈ 𝒜q} 𝟙(x ∈ ℬ^k_q(ℐ)) / p(x)` (p. 9). -/
noncomputable def W {n t K : ℕ} (μ : Measure (Table n t)) (I : Finset ℕ) (𝒜q : Finset (Fin n))
    (τs : Fin K → Table n t) : ℝ :=
  (1 / (K : ℝ)) * ∑ k, ∑ i ∈ 𝒜q, (if InBucket I (τs k) i then (1 : ℝ) else 0) / p μ I i

/-- One LSH Count estimate (p. 6): `Σ_{s=1}^S Z_s / S` for the samples `xs`. -/
noncomputable def estimate {n t K S : ℕ} (μ : Measure (Table n t)) (I : Finset ℕ)
    (𝒜q : Finset (Fin n)) (τs : Fin K → Table n t) (xs : Fin S → Fin K × Fin n) : ℝ :=
  (∑ s, Zval μ I 𝒜q τs (xs s)) / (S : ℝ)

/-- The (lower) median of `M` reals: the entry of index `⌊(M − 1)/2⌋` of the sorted list
(p. 15, "the median of these estimates"). It returns `0` when `M = 0`. -/
noncomputable def median {M : ℕ} (e : Fin M → ℝ) : ℝ :=
  ((List.ofFn e).insertionSort (· ≤ ·)).getD ((M - 1) / 2) 0

/-- The sampler's law given the tables (§4.3, p. 13; App. B, p. 35): uniform on the pool of
`(table, point)` pairs. If the pool is empty the sampler returns a uniform pair from all of
`Fin K × Fin n`, which is harmless because every weight `Zval` is `0` then. -/
noncomputable def samplerWeight {n t K : ℕ} (I : Finset ℕ) (τs : Fin K → Table n t)
    (y : Fin K × Fin n) : ℝ≥0∞ :=
  if (pool I τs).Nonempty then
    (if y ∈ pool I τs then ((pool I τs).card : ℝ≥0∞)⁻¹ else 0)
  else ((K * n : ℕ) : ℝ≥0∞)⁻¹

/-- One run of a single estimator on a probability space `(Ω, P)`: `T k` is the `k`-th table and
`X s` the `s`-th sample. The joint law is pinned: the `K` tables are i.i.d. with law `μ`, and given
the tables the `S` samples are i.i.d. with the sampler's law `samplerWeight` (drawn with
replacement). -/
def IsEstimatorRun {n t K S : ℕ} (μ : Measure (Table n t)) (I : Finset ℕ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (T : Fin K → Ω → Table n t) (X : Fin S → Ω → Fin K × Fin n) : Prop :=
  (∀ k, Measurable (T k)) ∧ (∀ s, Measurable (X s)) ∧
    ∀ (τs : Fin K → Table n t) (ξ : Fin S → Fin K × Fin n),
      P {ω | (∀ k, T k ω = τs k) ∧ ∀ s, X s ω = ξ s} =
        (∏ k, μ {τs k}) * ∏ s, samplerWeight I τs (ξ s)

/-- `M` independent runs of the estimator (median of means, p. 15): each run `m` is an estimator
run with fresh tables and samples, and the `M` runs are mutually independent. -/
def IsRun {n t K S M : ℕ} (μ : Measure (Table n t)) (I : Finset ℕ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (T : Fin M → Fin K → Ω → Table n t) (X : Fin M → Fin S → Ω → Fin K × Fin n) : Prop :=
  (∀ m, IsEstimatorRun μ I P (T m) (X m)) ∧
    iIndepFun (fun m ω => ((fun k => T m k ω), (fun s => X m s ω))) P

end LocalDensityLSH.Count


