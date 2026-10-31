-- Prove2me | Definitions.Def_CompositeSAA_excess
-- name    : CompositeSAA_excess
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:31:45.088783+00:00
-- url     : https://prove2.me/theorems/69d93bea-32ed-4669-abf5-0c8c28e61a27
-- title:
--   One-sided distance $\mathsf d(A,B)=\sup_{x\in A}\inf_{y\in B}\|x-y\|$
-- statement:
--   For sets $A,B$ in a metric space, the **one-sided distance** (excess) of $A$ to $B$ is
--
--   $$
--   \mathsf d(A,B)=\sup_{x\in A}d(x,B)=\sup_{x\in A}\inf_{y\in B}\|x-y\|,
--   $$
--
--   and the Pompeiu–Hausdorff distance is $\mathsf D(A,B)=\max\{\mathsf d(A,B),\mathsf d(B,A)\}$. The convergence $\mathsf d(S_N,S)\to0$ says that the approximate solution sets $S_N$ eventually lie in any neighbourhood of the true solution set $S$.
--
--   **Formalization Note** Valued in $[0,\infty]$, so that $\mathsf d(A,\emptyset)=\infty$ for nonempty $A$ and $\mathsf d(\emptyset,B)=0$. $\mathsf D$ is Mathlib's `Metric.hausdorffEDist`.
-- source:
--   Dentcheva, Lin, Penev, arXiv:2201.01338v1, p.4

import Mathlib

open scoped ENNReal

namespace CompositeSAA

/-- Dentcheva, Lin, Penev, arXiv:2201.01338v1, p.4: the one-sided distance (excess) of a set `A` to
a set `B`,

`d(A, B) = sup_{x ∈ A} d(x, B) = sup_{x ∈ A} inf_{y ∈ B} ‖x − y‖`.

The Pompeiu–Hausdorff distance `D(A, B) = max{d(A, B), d(B, A)}` of p.4 is Mathlib's
`Metric.hausdorffEDist A B`.

**Formalization Note** Valued in `ℝ≥0∞`, so that the supremum over an unbounded set and the
infimum over the empty set (`= ∞`) keep their meaning; `d(∅, B) = 0`. -/
noncomputable def excess {α : Type*} [PseudoEMetricSpace α] (A B : Set α) : ℝ≥0∞ :=
  ⨆ x ∈ A, Metric.infEDist x B

end CompositeSAA


