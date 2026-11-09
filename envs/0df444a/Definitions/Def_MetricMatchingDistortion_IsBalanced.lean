-- Prove2me | Definitions.Def_MetricMatchingDistortion_IsBalanced
-- name    : MetricMatchingDistortion_IsBalanced
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:15:40.699588+00:00
-- url     : https://prove2.me/theorems/4592917c-9986-46c2-8de6-746187bb711a
-- title:
--   Balanced partitions, cluster weights $w_j$ and partition cost $W(\mathcal P,d)$
-- statement:
--   A **balanced partition** $\mathcal P=(A_j,B_j)_{j}$ partitions the agents into $A_j$ and the items into $B_j$ with $|A_j|=|B_j|$ for every $j$; $A_j\cup B_j$ is a cluster. For a distance $d$,
--   $$w_j=\max_{a\in A_j,\ b\in B_j}d(a,b),\qquad W(\mathcal P,d)=\sum_j w_j .$$
--
--   **Formalization Note** A partition is a labelling of agents and items by labels in $\{0,\dots,n-1\}$; unused labels have no agent and no item. $w_j$ is computed as the maximum of $0$ and the distances in the cluster, which is the page's maximum for nonnegative $d$ and $0$ for an unused label.
-- source:
--   Charikar, Haqi, Hastings, Huang, Ramakrishnan, Sublinear Metric Distortion for Matching, arXiv:2611.05777 (held version, sha256 fdf3452b105082d6ff680c8a762ec950298417efdebeb216b721705a9802e0da), Definition 3.1, p.12 (PDF p.14)

import Mathlib

namespace MetricMatchingDistortion

/-- **Balanced partition.** Charikar et al., *Sublinear Metric Distortion for Matching*,
arXiv:2611.05777 (held version, sha256 fdf3452b…), Definition 3.1, p.12 (PDF p.14): "A balanced
partition is a family P = (Aj, Bj)_{j=1}^m such that (Aj)j partitions A, (Bj)j partitions B, and
|Aj| = |Bj| for every j. For each j, we refer to Aj ∪ Bj as a cluster."

A partition of agents and items into clusters is a labelling `c : Fin n ⊕ Fin n → Fin n`: agent
`a` lies in cluster `c (Sum.inl a)`, item `b` in cluster `c (Sum.inr b)`. It is balanced when every
label has as many agents as items.

**Formalization Note.** Labels are `Fin n`; a partition into `m ≤ n` nonempty clusters is a
labelling whose other `n − m` labels are unused. Unused labels have no agent and no item, so they
satisfy the balance condition and contribute nothing below. -/
def IsBalanced {n : ℕ} (c : Fin n ⊕ Fin n → Fin n) : Prop :=
  ∀ j, (Finset.univ.filter fun a => c (Sum.inl a) = j).card =
    (Finset.univ.filter fun b => c (Sum.inr b) = j).card

/-- `A_j`: the agents of cluster `j`. -/
def clusterAgents {n : ℕ} (c : Fin n ⊕ Fin n → Fin n) (j : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun a => c (Sum.inl a) = j

/-- `w_j = max_{a∈A_j, b∈B_j} d(a, b)` (Definition 3.1, p.12): the largest agent–item distance
inside cluster `j`.

**Formalization Note.** Computed as the maximum of `0` and these distances; for nonnegative `d` and
a nonempty cluster this is the page's maximum, and an unused label gets `0`. -/
def clusterWeight {n : ℕ} (c : Fin n ⊕ Fin n → Fin n) (d : Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ)
    (j : Fin n) : ℝ :=
  ((Finset.univ : Finset (Fin n × Fin n)).filter
      fun p => c (Sum.inl p.1) = j ∧ c (Sum.inr p.2) = j).fold max 0
    fun p => d (Sum.inl p.1) (Sum.inr p.2)

/-- The **partition cost** `W(P, d) = ∑_{j=1}^m w_j` (Definition 3.1, p.12). -/
def partitionCost {n : ℕ} (c : Fin n ⊕ Fin n → Fin n) (d : Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ) :
    ℝ :=
  ∑ j, clusterWeight c d j

end MetricMatchingDistortion


