-- Prove2me | Definitions.Def_SecSampling_FractionalSelection
-- name    : SecSampling_FractionalSelection
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:31:45.471394+00:00
-- url     : https://prove2.me/theorems/c6d93fe9-e375-4a5a-8a78-24ebdeaaa038
-- title:
--   Valid fractional selections, removed fraction, window average, local operators and the fill-in strategy
-- statement:
--   A **valid randomized algorithm** in the conflict graph (p.25) is a selection probability $q_s(v)\ge0$ on every node such that $\sum_{v\in P}q_s(v)\le 1$ along every monotone path $P$. The **removed fraction** $q_r(v)$ of a node is the sum of $q_s$ over the nodes of which $v$ is a descendant. The **performance** at size $s$ is $\sum_{|I|=s}p^{m(I)}(1-p)^{s-m(I)}q_s(I)$ (p.18), and the **average performance** in the window $[n,n+t]$ is the average of the performances at the $t+1$ sizes $s\in[n,n+t]$ (p.21).
--
--   The two **local operators** of Lemma 20 (p.25) at a node $v$:
--   1. set $q_s(v)=0$ and increase $q_s$ of each child of $v$ by the old $q_s(v)$;
--   2. raise $q_s(v)$ to $1-q_r(v)$ and set $q_s(v')=0$ for every descendant $v'$ of $v$.
--
--   The **fill-in strategy** for the window $[n,n+t]$ (p.22) scans the sizes in increasing order and selects all non-removed nodes of degree at most $\lfloor 1/(1-p)\rfloor$ at each size $s\in[n,n+t-1]$, and all non-removed nodes at size $n+t$; a node is removed when it is a descendant of a node selected at a smaller size. It selects nothing outside the window.
--
--   These are the objects of the window argument (Lemmas 17–20).
--
--   **Formalization Note.** Validity is required on finite monotone paths; for nonnegative terms this is the same as on infinite ones. The printed "$q_r(v')=1$" of operator 2 is not an assignment: the removed fraction is always computed from $q_s$. The all-ones string has degree $0$ and is selected by fill-in at every size of the window.
-- source:
--   J. Correa, A. Cristi, L. Feuilloley, T. Oosterwijk & A. Tsigonias-Dimitriadis, The Secretary Problem with Independent Sampling, arXiv:2011.07869v1, https://arxiv.org/abs/2011.07869v1, §5.4, p.21 (average performance), p.22 (fill-in strategy, PDF p.23), p.25 (valid randomized algorithm, removed fraction, Lemma 20's operators, PDF p.26); §5.2.2, p.18 (performance)

import Mathlib
import Definitions.Def_SecSampling_ConflictGraph

open Classical

namespace SecSampling

/-- A **valid (randomized) algorithm in the conflict graph** (arXiv:2011.07869v1, §5.4, p.25): a
nonnegative selection probability `qs(v)` on every node such that the sum of `qs(v)` over all
vertices of any monotone path is at most `1`.

**Formalization Note.** Only finite monotone paths are quantified; for nonnegative terms the
condition for possibly infinite paths (p.15) is the same, since every partial sum is bounded. -/
def IsValidSel (qs : List Bool → ℝ) : Prop :=
  (∀ I, 0 ≤ qs I) ∧ ∀ P : List (List Bool), IsMonotonePath P → (P.map qs).sum ≤ 1

/-- The **removed fraction** `q_r(v)` of a node (p.18 and p.25, "cf. Lemma 13"): the sum of the
selection probabilities of the nodes of which `v` is a descendant (its strict ancestors). -/
noncomputable def removedFrac (qs : List Bool → ℝ) (v : List Bool) : ℝ :=
  ∑ s ∈ Finset.range v.length, ∑ I ∈ (strings s).filter (fun I => IsDescendant I v), qs I

/-- The **performance** at size `s` of a selection `qs` (p.18): "the product of the weight of a
node multiplied by its selection probability, summed over all instances of size n". -/
noncomputable def perfSel (p : ℝ) (qs : List Bool → ℝ) (s : ℕ) : ℝ :=
  ∑ I ∈ strings s, weight p I * qs I

/-- The **average performance** in the window `[n, n + t]` (p.21): the average of the performance
over the `t + 1` sizes `s ∈ [n, n + t]`. -/
noncomputable def windowAvg (p : ℝ) (qs : List Bool → ℝ) (n t : ℕ) : ℝ :=
  (∑ s ∈ Finset.Icc n (n + t), perfSel p qs s) / ((t : ℝ) + 1)

/-- The **first local operator** of Lemma 20 (p.25) at node `v`: set `qs(v) = 0` and increase the
selection probability of each child of `v` by `qs(v)`. -/
noncomputable def localOp1 (qs : List Bool → ℝ) (v : List Bool) : List Bool → ℝ := fun w =>
  if w = v then 0 else if Edge v w then qs w + qs v else qs w

/-- The **second local operator** of Lemma 20 (p.25) at node `v`: increase `qs(v)` by
`ε = 1 − qs(v) − q_r(v)` (so the new value is `1 − q_r(v)`), and set `qs(v′) = 0` for every
descendant `v′` of `v`.

**Formalization Note.** The printed "and `q_r(v′) = 1`" is a consequence, not an assignment:
`q_r` is computed from `qs` by `removedFrac`. -/
noncomputable def localOp2 (qs : List Bool → ℝ) (v : List Bool) : List Bool → ℝ := fun w =>
  if w = v then 1 - removedFrac qs v else if IsDescendant v w then 0 else qs w

/-- The nodes of size `s` selected by the **fill-in strategy** for the window `[n, n + t]`
(p.22: it "scans the sizes in increasing order, selects all the non-removed instances of degree
up to ⌊1/(1−p)⌋ for each size s ∈ [n, n + t − 1], and all the non-removed instances for size
n + t"). A node is removed when it is a descendant of a node selected at an earlier size.

**Formalization Note.** Nothing is selected outside the window. The all-ones string has degree
`0` and counts as "degree up to ⌊1/(1−p)⌋". -/
noncomputable def fillSet (p : ℝ) (n t : ℕ) (s : ℕ) : Finset (List Bool) :=
  if n ≤ s ∧ s ≤ n + t then
    (strings s).filter (fun I => (s < n + t → degree I ≤ kOf p) ∧
      ∀ s' : Fin s, ∀ J ∈ fillSet p n t s', ¬ IsDescendant J I)
  else ∅
termination_by s
decreasing_by all_goals exact Fin.isLt _

/-- The **fill-in strategy** for the window `[n, n + t]` as a (0/1-valued) selection. -/
noncomputable def fillIn (p : ℝ) (n t : ℕ) (I : List Bool) : ℝ :=
  if I ∈ fillSet p n t I.length then 1 else 0

end SecSampling


