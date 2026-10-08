-- Prove2me | Definitions.Def_UnrelatedSched_TwoTimes_Theorem4Instance
-- name    : UnrelatedSched_TwoTimes_Theorem4Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T05:05:06.920841+00:00
-- url     : https://prove2.me/theorems/9e791132-331b-447c-a174-35adfebeae10
-- title:
--   3-dimensional matching and the scheduling instance of Theorem 4 (times in $\{1,3\}$)
-- statement:
--   This file fixes the objects of the reduction in the proof of Theorem 4 of Lenstra, Shmoys and Tardos.
--
--   **3-dimensional matching.** An instance consists of three disjoint sets $A=\{a_1,\dots,a_n\}$, $B=\{b_1,\dots,b_n\}$, $C=\{c_1,\dots,c_n\}$ and a family $F=\{T_1,\dots,T_m\}$ of triples with $|T_i\cap A|=|T_i\cap B|=|T_i\cap C|=1$; we write $T_i=(a_j,b_k,c_l)$. A **matching** is a subfamily $F'\subseteq F$ with
--
--   $$|F'|=n \quad\text{and}\quad \bigcup_{T_i\in F'} T_i = A\cup B\cup C .$$
--
--   **The scheduling instance.** From such an instance build a scheduling instance with $m$ machines, machine $i$ corresponding to the triple $T_i$, and $3n+(m-n)$ jobs: $3n$ *element jobs*, one for each element of $A\cup B\cup C$, and $m-n$ *dummy jobs*. Machine $i$, with $T_i=(a_j,b_k,c_l)$, processes each of the element jobs of $a_j$, $b_k$ and $c_l$ in one time unit and every other job in three time units; in particular every dummy job takes three time units on every machine. Thus
--
--   $$p_{i,x}=\begin{cases}1 & \text{if $x$ is the element job of an element of } T_i,\\ 3 & \text{otherwise.}\end{cases}$$
--
--   Two simplification lemmas record the processing time of an element job and of a dummy job.
--
--   **Formalization Note** The elements $a_j,b_k,c_l$ are indexed by $j,k,l\in\{0,\dots,n-1\}$ (`Fin n`) and $T_i$ is the triple of indices $(j,k,l)$; the family is indexed by `Fin m`, so a triple may occur more than once. A subfamily is a set of indices. The element jobs are indexed by a coordinate $c\in\{0,1,2\}$ (for $A$, $B$, $C$) and an index $x$, and all $3n+(m-n)$ jobs are enumerated as `Fin (3 * n + (m - n))`, element jobs first, so that the published load and makespan of `MatousekLP.Scheduling.Schedule` apply. When $m<n$ the natural-number subtraction gives $m-n=0$ dummy jobs; the paper instead uses "some trivial 'no' instance" there, and the instance built here is also a "no" instance in that case.
-- source:
--   Lenstra, Shmoys, Tardos, Approximation algorithms for scheduling unrelated parallel machines, CWI Report OS-R8714 (1987), p. 7, §4, proof of Theorem 4 (3-DIMENSIONAL MATCHING and the reduction)

import Mathlib

namespace UnrelatedSched.TwoTimes

/-- A matching of an instance of 3-DIMENSIONAL MATCHING (Lenstra, Shmoys, Tardos, CWI Report
OS-R8714 (1987), §4, p. 7, proof of Theorem 4).

The instance consists of disjoint sets `A = {a_1, …, a_n}`, `B = {b_1, …, b_n}`,
`C = {c_1, …, c_n}` and a family `F = {T_1, …, T_m}` of triples with `|T_i ∩ A| = |T_i ∩ B| =
|T_i ∩ C| = 1`. The elements `a_j`, `b_k`, `c_l` are indexed by `j, k, l : Fin n`, and the triple
`T_i` is `T i = (j, k, l)`, standing for `(a_j, b_k, c_l)`; the triples are indexed by `i : Fin m`,
so the same triple may occur several times in the family.

A matching is a subfamily `F'`, given by its index set `F' : Finset (Fin m)`, with `|F'| = n`
whose union is `A ∪ B ∪ C`: every `a_j`, every `b_k` and every `c_l` lies in some triple of `F'`. -/
def IsThreeDimMatching {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) (F' : Finset (Fin m)) :
    Prop :=
  F'.card = n ∧
    (∀ j : Fin n, ∃ i ∈ F', (T i).1 = j) ∧
    (∀ k : Fin n, ∃ i ∈ F', (T i).2.1 = k) ∧
    (∀ l : Fin n, ∃ i ∈ F', (T i).2.2 = l)

/-- The three coordinates of a triple `t = (j, k, l)`: coordinate `0` is the `A`-index `j`,
coordinate `1` the `B`-index `k`, coordinate `2` the `C`-index `l`. -/
def tripleCoord {n : ℕ} (t : Fin n × Fin n × Fin n) : Fin 3 → Fin n :=
  ![t.1, t.2.1, t.2.2]

/-- The element job of the scheduling instance of Theorem 4 corresponding to an element of
`A ∪ B ∪ C`: `thm4ElemJob m c x` is the job of `a_x` if `c = 0`, of `b_x` if `c = 1`, of `c_x`
if `c = 2`. The `3n + (m - n)` jobs are enumerated as `Fin (3 * n + (m - n))`, the `3n` element
jobs first (as `Fin 3 × Fin n ≃ Fin (3 * n)`), then the `m - n` dummy jobs. -/
def thm4ElemJob {n : ℕ} (m : ℕ) (c : Fin 3) (x : Fin n) : Fin (3 * n + (m - n)) :=
  finSumFinEquiv (Sum.inl (finProdFinEquiv (c, x)))

/-- The `k`-th dummy job of the scheduling instance of Theorem 4, `k : Fin (m - n)`. -/
def thm4DummyJob {n m : ℕ} (k : Fin (m - n)) : Fin (3 * n + (m - n)) :=
  finSumFinEquiv (Sum.inr k)

/-- The processing times of the scheduling instance built from a 3-DIMENSIONAL MATCHING instance
`T` in the proof of Theorem 4 (p. 7): `m` machines, machine `i` corresponding to the triple
`T_i = (a_j, b_k, c_l)`; `3n` element jobs and `m - n` dummy jobs. Machine `i` processes each of
the jobs of `a_j`, `b_k`, `c_l` in one time unit and every other job in three time units; the
dummy jobs require three time units on each machine. -/
def thm4Times {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) :
    Matrix (Fin m) (Fin (3 * n + (m - n))) ℕ :=
  fun i j =>
    Sum.elim
      (fun e => if tripleCoord (T i) (finProdFinEquiv.symm e).1 = (finProdFinEquiv.symm e).2
        then 1 else 3)
      (fun _ => 3) (finSumFinEquiv.symm j)

@[simp] theorem thm4Times_elem {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) (i : Fin m)
    (c : Fin 3) (x : Fin n) :
    thm4Times T i (thm4ElemJob m c x) = if tripleCoord (T i) c = x then 1 else 3 := by
  simp only [thm4Times, thm4ElemJob, Equiv.symm_apply_apply, Sum.elim_inl]

@[simp] theorem thm4Times_dummy {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) (i : Fin m)
    (k : Fin (m - n)) : thm4Times T i (thm4DummyJob k) = 3 := by
  simp [thm4Times, thm4DummyJob]

end UnrelatedSched.TwoTimes


