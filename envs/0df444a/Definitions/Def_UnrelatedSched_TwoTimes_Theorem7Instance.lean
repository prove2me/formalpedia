-- Prove2me | Definitions.Def_UnrelatedSched_TwoTimes_Theorem7Instance
-- name    : UnrelatedSched_TwoTimes_Theorem7Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T05:05:06.199884+00:00
-- url     : https://prove2.me/theorems/9d58b113-64bd-48be-8f58-93475a7d94f3
-- title:
--   q-dimensional matching and the scheduling instance of Theorem 7 (times in $\{p,q\}$)
-- statement:
--   This file fixes the objects of the reduction in the proof of Theorem 7 of Lenstra, Shmoys and Tardos.
--
--   **q-dimensional matching.** An instance consists of a ground set $U$ of $qn$ elements and a family $S_1,\dots,S_m$ of $q$-element subsets ("$q$-tuples") of $U$. A **matching** is a subfamily $F'\subseteq\{1,\dots,m\}$ with
--
--   $$|F'|=n \quad\text{and}\quad \bigcup_{i\in F'} S_i = U .$$
--
--   Since $n$ sets of size $q$ cover the $qn$ elements of $U$, the tuples of a matching are pairwise disjoint.
--
--   **The scheduling instance.** Given natural numbers $p$ and $q$, build a scheduling instance with $m$ machines, machine $i$ corresponding to the tuple $S_i$, and $qn+p(m-n)$ jobs: $qn$ *element jobs*, one for each $u\in U$, and $p(m-n)$ *dummy jobs*. An element job can be processed in $p$ time units by each machine whose tuple contains the corresponding element; all other processing times are $q$ time units:
--
--   $$p_{i,u}=\begin{cases}p & u\in S_i,\\ q & u\notin S_i,\end{cases}\qquad p_{i,d}=q\ \text{ for every dummy job } d .$$
--
--   Two simplification lemmas record the processing time of an element job and of a dummy job.
--
--   **Formalization Note** The ground set is `Fin (q * n)` and the family is `S : Fin m → Finset (Fin (q * n))`, indexed by machines, so a tuple may occur more than once; the condition $|S_i|=q$ is a hypothesis of the theorems that need it. The q-partite structure of q-dimensional matching (one element from each of $q$ classes) is not imposed: the paper's reduction does not use it, and the statements over arbitrary families of $q$-sets contain the q-partite case. All $qn+p(m-n)$ jobs are enumerated as `Fin (q * n + p * (m - n))`, element jobs first, so that the published load and makespan of `MatousekLP.Scheduling.Schedule` apply. When $m<n$ the natural-number subtraction gives no dummy jobs.
-- source:
--   Lenstra, Shmoys, Tardos, Approximation algorithms for scheduling unrelated parallel machines, CWI Report OS-R8714 (1987), pp. 8-9, §5, proof of Theorem 7

import Mathlib

namespace UnrelatedSched.TwoTimes

/-- A matching of an instance of q-dimensional matching (Lenstra, Shmoys, Tardos, CWI Report
OS-R8714 (1987), §5, proof of Theorem 7, p. 8: "a matching instance with m q-tuples over a ground
set of qn elements").

The ground set is `Fin (q * n)` and the family is `S : Fin m → Finset (Fin (q * n))`, indexed by
`i : Fin m` (repeated sets allowed); the theorems that use it assume `(S i).card = q`. A matching is
a subfamily, given by its index set `F' : Finset (Fin m)`, with `|F'| = n` whose union is the whole
ground set. The q-partite structure of q-dimensional matching is not imposed: families of q-sets
include the q-partite families. -/
def IsQMatching {q n m : ℕ} (S : Fin m → Finset (Fin (q * n))) (F' : Finset (Fin m)) : Prop :=
  F'.card = n ∧ F'.biUnion S = Finset.univ

/-- The element job of the scheduling instance of Theorem 7 corresponding to the element
`u` of the ground set. The `qn + p(m - n)` jobs are enumerated as `Fin (q * n + p * (m - n))`,
the `qn` element jobs first, then the `p(m - n)` dummy jobs. -/
def elemJob (p q n m : ℕ) (u : Fin (q * n)) : Fin (q * n + p * (m - n)) :=
  finSumFinEquiv (Sum.inl u)

/-- The `k`-th dummy job of the scheduling instance of Theorem 7, `k : Fin (p * (m - n))`. -/
def dummyJob (p q n m : ℕ) (k : Fin (p * (m - n))) : Fin (q * n + p * (m - n)) :=
  finSumFinEquiv (Sum.inr k)

/-- The processing times of the scheduling instance built in the proof of Theorem 7 (pp. 8–9)
from a q-dimensional matching instance `S` with `m` tuples over a ground set of `qn` elements:
`m` machines (machine `i` corresponds to the tuple `S i`), `qn` element jobs and `p(m - n)` dummy
jobs. An element job takes `p` time units on each machine whose tuple contains the corresponding
element; all other processing times are `q` time units. -/
def twoTimes (p q n : ℕ) {m : ℕ} (S : Fin m → Finset (Fin (q * n))) :
    Matrix (Fin m) (Fin (q * n + p * (m - n))) ℕ :=
  fun i j => Sum.elim (fun u => if u ∈ S i then p else q) (fun _ => q) (finSumFinEquiv.symm j)

@[simp] theorem twoTimes_elem (p q n : ℕ) {m : ℕ} (S : Fin m → Finset (Fin (q * n))) (i : Fin m)
    (u : Fin (q * n)) : twoTimes p q n S i (elemJob p q n m u) = if u ∈ S i then p else q := by
  simp [twoTimes, elemJob]

@[simp] theorem twoTimes_dummy (p q n : ℕ) {m : ℕ} (S : Fin m → Finset (Fin (q * n))) (i : Fin m)
    (k : Fin (p * (m - n))) : twoTimes p q n S i (dummyJob p q n m k) = q := by
  simp [twoTimes, dummyJob]

end UnrelatedSched.TwoTimes


