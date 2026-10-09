-- Prove2me | Definitions.Def_GreedWorks_OnlineList_Greedy
-- name    : GreedWorks_OnlineList_Greedy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T22:12:12.639261+00:00
-- url     : https://prove2.me/theorems/1978ca2a-7bc9-4cf8-b52d-cc50721ad098
-- title:
--   §4, pp. 8–9 — greedy assignment and WSEPT sequencing
-- statement:
--   For each eligible pair $(i,j)$, let $\mu_{ij}=\mathbb E[P_{ij}]$. On machine $i$, a job $k$ has at least the **WSEPT priority** of $j$ when $w_k/\mu_{ik}>w_j/\mu_{ij}$, or the ratios are equal and $k\le j$. Denote these jobs by $H(j,i)$; its complement is $L(j,i)$. Jobs are indexed by arrival order.
--
--   When $j$ arrives, its assignment cost on eligible machine $i$, given the assignments of jobs $k<j$, is
--
--   $$\operatorname{cost}(j\to i)=w_j\left(\mu_{ij}+\sum_{\substack{k<j,\,m(k)=i\\k\in H(j,i)}}\mu_{ik}\right)+\mu_{ij}\sum_{\substack{k<j,\,m(k)=i\\k\in L(j,i)}}w_k.$$
--
--   A **greedy assignment** chooses any eligible machine minimizing this cost. After all jobs arrive, each machine runs its assigned jobs without idle time in WSEPT order. The realized completion time of $j$ is the sum of the realized processing times of the assigned jobs in $H(j,m(j))$; $\mathrm{ALG}$ is the expectation of the resulting weighted completion sum. The module also defines the paper's dual-fitting quantities $\alpha_j$, nominal completion times and unfinished-weight quantities $\beta_{is}$, plus their speed-$f$ versions.
--
--   This is the algorithm assessed in Theorem 1. **Formalization Note** The cost reads assignments only for earlier jobs; ties in the machine minimum are arbitrary, while equal WSEPT ratios use job index. Ineligible pairs never contribute to a schedule.
-- source:
--   Gupta, Moseley, Uetz & Xie, Greed Works – Online Algorithms For Unrelated Machine Stochastic Scheduling, arXiv:1703.01634v4, pp. 8–10, §4 and §5

import Mathlib
import Definitions.Def_GreedWorks_OnlineList_Model

namespace GreedWorks.OnlineList

open MeasureTheory

variable {M : Type*} [Fintype M] [DecidableEq M] {n : ℕ}
  {Ω : Type*} [MeasurableSpace Ω]

/-- The jobs with at least the WSEPT priority of `j` on machine `i`, with index
tie-breaking.  Only eligible jobs are used in a schedule on `i`. -/
noncomputable def high (I : StochasticInstance M n Ω) (j : Fin n) (i : M) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun k =>
    I.weight j / mean I i j < I.weight k / mean I i k ∨
      (k ≤ j ∧ I.weight k / mean I i k = I.weight j / mean I i j)

/-- Jobs of lower WSEPT priority than `j` on machine `i`. -/
noncomputable def low (I : StochasticInstance M n Ω) (j : Fin n) (i : M) : Finset (Fin n) := by
  classical
  exact Finset.univ \ high I j i

/-- The expected increase in weighted completion time when the new job `j` is put on
machine `i`.  The assignment is read only for earlier jobs. -/
noncomputable def incrementalCost (I : StochasticInstance M n Ω)
    (m : Fin n → M) (j : Fin n) (i : M) : ℝ := by
  classical
  exact I.weight j *
      (mean I i j + ∑ k ∈ (Finset.univ.filter fun k : Fin n =>
        k < j ∧ m k = i ∧ k ∈ high I j i), mean I i k) +
    mean I i j * ∑ k ∈ (Finset.univ.filter fun k : Fin n =>
      k < j ∧ m k = i ∧ k ∈ low I j i), I.weight k

/-- Every arriving job is sent to any eligible minimizer of its instantaneous cost.
The condition allows every possible way of breaking ties. -/
def IsGreedy (I : StochasticInstance M n Ω) (m : Fin n → M) : Prop :=
  ∀ j, I.eligible (m j) j ∧
    ∀ i, I.eligible i j → incrementalCost I m j (m j) ≤ incrementalCost I m j i

/-- Realized completion time in the fixed-assignment, no-idle WSEPT schedule. -/
noncomputable def algorithmCompletion (I : StochasticInstance M n Ω)
    (m : Fin n → M) (j : Fin n) (ω : Ω) : ℝ := by
  classical
  exact ∑ k ∈ (Finset.univ.filter fun k : Fin n =>
    m k = m j ∧ k ∈ high I j (m j)), (I.P (m j) k ω : ℝ)

/-- The objective of the realized WSEPT schedule, before taking its expectation. -/
noncomputable def algorithmCost (I : StochasticInstance M n Ω)
    (m : Fin n → M) : ℝ :=
  ∫ ω, ∑ j : Fin n, I.weight j * algorithmCompletion I m j ω ∂I.Pr

/-- Dual-fitting quantity α, the cost incurred when `j` is assigned. -/
noncomputable def alpha (I : StochasticInstance M n Ω)
    (m : Fin n → M) (j : Fin n) : ℝ := incrementalCost I m j (m j)

/-- Completion time of `j` when processing times equal their means. -/
noncomputable def nominalCompletion (I : StochasticInstance M n Ω)
    (m : Fin n → M) (j : Fin n) : ℝ := by
  classical
  exact ∑ k ∈ (Finset.univ.filter fun k : Fin n =>
    m k = m j ∧ k ∈ high I j (m j)), mean I (m j) k

/-- Dual-fitting quantity β, the total weight of assigned jobs unfinished at integer
time `s` in the nominal schedule. -/
noncomputable def beta (I : StochasticInstance M n Ω)
    (m : Fin n → M) (i : M) (s : ℕ) : ℝ := by
  classical
  exact ∑ k ∈ (Finset.univ.filter fun k : Fin n =>
    m k = i ∧ (s : ℝ) < nominalCompletion I m k), I.weight k

/-- Mean processing time in the speed-`f` nominal instance. -/
noncomputable def fastMean (I : StochasticInstance M n Ω)
    (f : ℕ) (i : M) (j : Fin n) : ℝ := mean I i j / (f : ℝ)

/-- WSEPT priority computed on the speed-`f` instance.  For positive `f` this
coincides with `high I j i`. -/
noncomputable def highFast (I : StochasticInstance M n Ω)
    (f : ℕ) (j : Fin n) (i : M) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun k =>
    I.weight j / fastMean I f i j < I.weight k / fastMean I f i k ∨
      (k ≤ j ∧ I.weight k / fastMean I f i k = I.weight j / fastMean I f i j)

noncomputable def lowFast (I : StochasticInstance M n Ω)
    (f : ℕ) (j : Fin n) (i : M) : Finset (Fin n) := by
  classical
  exact Finset.univ \ highFast I f j i

/-- Instantaneous assignment cost computed from speed-`f` mean processing times. -/
noncomputable def incrementalCostFast (I : StochasticInstance M n Ω)
    (m : Fin n → M) (f : ℕ) (j : Fin n) (i : M) : ℝ := by
  classical
  exact I.weight j *
      (fastMean I f i j + ∑ k ∈ (Finset.univ.filter fun k : Fin n =>
        k < j ∧ m k = i ∧ k ∈ highFast I f j i), fastMean I f i k) +
    fastMean I f i j * ∑ k ∈ (Finset.univ.filter fun k : Fin n =>
      k < j ∧ m k = i ∧ k ∈ lowFast I f j i), I.weight k

/-- α of the actual speed-`f` nominal instance. -/
noncomputable def alphaFast (I : StochasticInstance M n Ω)
    (m : Fin n → M) (f : ℕ) (j : Fin n) : ℝ :=
  incrementalCostFast I m f j (m j)

/-- Completion time in the speed-`f` nominal schedule. -/
noncomputable def nominalCompletionFast (I : StochasticInstance M n Ω)
    (m : Fin n → M) (f : ℕ) (j : Fin n) : ℝ := by
  classical
  exact ∑ k ∈ (Finset.univ.filter fun k : Fin n =>
    m k = m j ∧ k ∈ highFast I f j (m j)), fastMean I f (m j) k

/-- β from the nominal schedule whose processing times have been divided by `f`.
At positive integer `f` it equals `β i (f * s)`. -/
noncomputable def betaFast (I : StochasticInstance M n Ω)
    (m : Fin n → M) (f : ℕ) (i : M) (s : ℕ) : ℝ := by
  classical
  exact ∑ k ∈ (Finset.univ.filter fun k : Fin n =>
    m k = i ∧ (s : ℝ) < nominalCompletionFast I m f k), I.weight k

end GreedWorks.OnlineList


