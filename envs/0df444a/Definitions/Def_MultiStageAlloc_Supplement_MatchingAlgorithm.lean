-- Prove2me | Definitions.Def_MultiStageAlloc_Supplement_MatchingAlgorithm
-- name    : MultiStageAlloc_Supplement_MatchingAlgorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:19:18.490364+00:00
-- url     : https://prove2.me/theorems/fff3f1ae-b2e8-59e8-b814-e9e1a4a0d87c
-- title:
--   Deterministic and randomized multi-stage fractional matching algorithms and their expected value
-- statement:
--   Fix the number of stages $K$. Instances are those of the multi-stage matching model: online vertices arriving in batches $U_1,\dots,U_K$, edges, offline weights $w_j\ge0$ and capacities $n_j>0$.
--
--   A **feasible allocation** of an instance is a family $x_{k,ij}\ge0$ such that
--
--   1. $x_{k,ij}>0$ only on edges $(i,j)$ with $i\in U_k$;
--   2. $\sum_j x_{k,ij}\le1$ for every stage $k$ and online vertex $i$;
--   3. $\sum_{k\in[K]}\sum_i x_{k,ij}\le n_j$ for every offline vertex $j$.
--
--   A **deterministic multi-stage fractional matching algorithm** maps every finite instance (on $n$ online and $m$ offline vertices) to a feasible allocation and is non-anticipating: its allocations at stages $s\le k$ coincide on any two instances that agree on what is revealed by the end of stage $k$. That is the offline data $w,n$, and the arrival stage and incident edges of every online vertex arriving at a stage $\le k$.
--
--   A **randomized algorithm** is a probability space $(\Omega,\mu)$ and a deterministic algorithm $A_\omega$ for each $\omega\in\Omega$, such that the total weight $\omega\mapsto\mathrm{ALG}(I,A_\omega)=\sum_{k}\sum_{i,j}w_jx_{k,ij}$ is measurable for every instance. Its value on $I$ is the expected total weight $\int\mathrm{ALG}(I,A_\omega)\,d\mu(\omega)$, as in Definition 1.
--
--   **Formalization Note** The algorithm may also read the numbers $n$ and $m$ of vertices. That enlarges the class of algorithms, which only strengthens an impossibility result. Integral algorithms are the $\{0,1\}$-valued special case, and a Dirac measure gives the deterministic case. The total weight is bounded by $\sum_jw_jn_j$, so the integral is the true expectation.
-- source:
--   Feng & Niazadeh, Batching and Optimal Multi-stage Bipartite Allocations, arXiv:2211.16581v1, §2.1, p.12, and Definition 1, p.14

import Mathlib
import Definitions.Def_MultiStageAlloc_Run

namespace MultiStageAlloc.Supplement

open MeasureTheory

/-- **A feasible multi-stage fractional allocation** of an instance of the matching model,
Feng & Niazadeh, arXiv:2211.16581v1, §2.1, p.12: `x k i j ≥ 0` is the amount of online vertex `i`
allocated to `j` at stage `k`; it is carried by `E_k` (an edge `(i, j)` with `batch i = k`); each
online vertex uses at most one unit, `∑_j x k i j ≤ 1`; and each offline vertex at most its capacity
over all stages, `∑_{k ∈ [K]} ∑_i x k i j ≤ n_j`. Integral allocations are the `{0,1}`-valued
special case. -/
def IsAllocation {U V : Type*} [Fintype U] [Fintype V] {K : ℕ} (I : Instance U V K)
    (x : ℕ → U → V → ℝ) : Prop :=
  (∀ k i j, 0 ≤ x k i j) ∧ (∀ k i j, x k i j ≠ 0 → I.edge i j ∧ I.batch i = k) ∧
    (∀ k i, ∑ j, x k i j ≤ 1) ∧ ∀ j, ∑ k ∈ Finset.Icc 1 K, ∑ i, x k i j ≤ I.cap j

/-- **Two instances agree on everything revealed by the end of stage `k`**: the same offline data
(`w`, `n`), and every online vertex that arrives at a stage `≤ k` in either instance arrives at the
same stage in both, with the same incident edges. -/
def AgreeUpTo {U V : Type*} {K : ℕ} (I I' : Instance U V K) (k : ℕ) : Prop :=
  I.w = I'.w ∧ I.cap = I'.cap ∧
    ∀ i, (I.batch i ≤ k ∨ I'.batch i ≤ k) → I.batch i = I'.batch i ∧ ∀ j, (I.edge i j ↔ I'.edge i j)

/-- **A deterministic multi-stage fractional matching algorithm** with `K` stages, arXiv:2211.16581v1,
§2.1, p.12 and §2.3, p.14. It maps every instance on `n` online and `m` offline vertices (every
finite instance, up to relabelling) to a feasible allocation, and it is non-anticipating: its
allocations at stages `s ≤ k` depend only on what is revealed by the end of stage `k`.

**Formalization Note.** The algorithm may also read the total numbers `n` and `m` of vertices; more
information only enlarges the class of algorithms. -/
structure MatchingAlgorithm (K : ℕ) where
  /-- The allocation produced on an instance. -/
  alloc : ∀ n m : ℕ, Instance (Fin n) (Fin m) K → ℕ → Fin n → Fin m → ℝ
  /-- Every output is a feasible allocation. -/
  feasible : ∀ n m (I : Instance (Fin n) (Fin m) K), IsAllocation I (alloc n m I)
  /-- Non-anticipation. -/
  nonanticipating : ∀ n m (I I' : Instance (Fin n) (Fin m) K) (k : ℕ), AgreeUpTo I I' k →
    ∀ s, s ≤ k → alloc n m I s = alloc n m I' s

/-- **A randomized multi-stage fractional matching algorithm**: a probability space `(Ω, μ)` and a
deterministic algorithm `alg ω` for each outcome `ω`, such that the total weight
`ω ↦ ALG(I, alg ω)` is measurable on every instance. A Dirac measure is a deterministic
algorithm. -/
structure RandomizedAlgorithm (K : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  /-- The law of the random seed. -/
  μ : Measure Ω
  /-- It is a probability measure. -/
  isProb : IsProbabilityMeasure μ
  /-- The deterministic algorithm run on seed `ω`. -/
  alg : Ω → MatchingAlgorithm K
  /-- The total weight is a random variable on every instance. -/
  measurable_value : ∀ n m (I : Instance (Fin n) (Fin m) K),
    Measurable fun ω => ALG I ((alg ω).alloc n m I)

/-- **The expected total weight `ALG(I)` of a randomized algorithm** on an instance, as in
Definition 1, arXiv:2211.16581v1, p.14 ("for randomized multi-stage algorithms … ALG(I) denotes the
expected total weight"). The integrand is bounded (by `∑_j w_j n_j`), so the Bochner integral is
the true expectation. -/
noncomputable def expectedALG {K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (R : RandomizedAlgorithm K Ω) {n m : ℕ} (I : Instance (Fin n) (Fin m) K) : ℝ :=
  ∫ ω, ALG I ((R.alg ω).alloc n m I) ∂(R.μ)

end MultiStageAlloc.Supplement


