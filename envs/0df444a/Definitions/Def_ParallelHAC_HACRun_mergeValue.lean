-- Prove2me | Definitions.Def_ParallelHAC_HACRun_mergeValue
-- name    : ParallelHAC_HACRun_mergeValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:15.681201+00:00
-- url     : https://prove2.me/theorems/af6a4a66-1d5c-41a6-9783-0873471502ac
-- title:
--   Merge values $\delta_i$ and running maximum $\tilde\delta=\max_{i\le s}\delta_i$
-- statement:
--   For a HAC run with merges $(A_i,B_i)$, the **value** of the $i$-th merge is $\delta_i:=d(A_i,B_i)$, and for $s\ge1$
--   $$\max_{1\le i\le s}\delta_i$$
--   is the largest value of a merge performed up to and including merge $s$. For the $j$-th phase starting at merge $s_j$ this is $\tilde\delta_j$.
--
--   **Formalization Note** For $s=0$ (never used) the value is $0$.
-- source:
--   Bateni, Dhulipala, Fletcher, Gowda, Hershkowitz, Jayaram, Łącki, Parallel Hierarchical Agglomerative Clustering in Low Dimensions, arXiv:2507.20047 (sha256 a21061c8…), §4 p.18 (PDF p.21); §4.1 p.19 (PDF p.22)

import Mathlib
import Definitions.Def_ParallelHAC_HACRun

namespace ParallelHAC

/-- `δ_i := d(A_i, B_i)`, the value of the `i`-th merge of a HAC run (§1, p.1; §4, p.18).
Source: arXiv:2507.20047 (sha256 a21061c8…), p.18. -/
def HACRun.mergeValue {V : Type*} [DecidableEq V] {P : Finset V}
    {d : Finset V → Finset V → ℝ} {c : ℝ} (R : HACRun P d c) (i : ℕ) : ℝ :=
  d (R.A i) (R.B i)

/-- `δ̃ = max_{1 ≤ i ≤ s} δ_i`, the largest value of a merge performed up to and including merge
`s` (§4.1, p.19; `δ̃_j` is `maxMergeValue s_j`).
Source: arXiv:2507.20047 (sha256 a21061c8…), §4.1, p.19.

**Formalization Note.** Merges are indexed from `1`; for `s = 0` (an empty range, never used) the
value is `0`. -/
noncomputable def HACRun.maxMergeValue {V : Type*} [DecidableEq V] {P : Finset V}
    {d : Finset V → Finset V → ℝ} {c : ℝ} (R : HACRun P d c) (s : ℕ) : ℝ :=
  if h : (Finset.Icc 1 s).Nonempty then (Finset.Icc 1 s).sup' h R.mergeValue else 0

end ParallelHAC


