-- Prove2me | Definitions.Def_ParallelHAC_HACRun_clusterOf
-- name    : ParallelHAC_HACRun_clusterOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:22.444206+00:00
-- url     : https://prove2.me/theorems/a720d122-f072-4cc1-bc2c-64c78af369b1
-- title:
--   The cluster $X_i$ of $x_0$, participation, and the partner $\bar X_i$
-- statement:
--   Fix a HAC run and a point $x_0\in P$. For a merge index $i$:
--
--   1. $X_i$ is the cluster of $\mathcal C_i$ containing $x_0$, just before the $i$-th merge.
--   2. $X_i$ **participates** in the $i$-th merge when $X_i\in\{A_i,B_i\}$.
--   3. In that case $\bar X_i$ is the cluster with which $X_i$ merges, the one element of $\{A_i,B_i\}\setminus\{X_i\}$.
--
--   These are the objects through which the proof of Theorem 3 follows a single point.
--
--   **Formalization Note** $X_i$ is written as the union of the members of $\mathcal C_i$ containing $x_0$, which is the unique such cluster because $\mathcal C_i$ partitions $P$. $\bar X_i$ is only meaningful when $X_i$ participates.
-- source:
--   Bateni, Dhulipala, Fletcher, Gowda, Hershkowitz, Jayaram, Łącki, Parallel Hierarchical Agglomerative Clustering in Low Dimensions, arXiv:2507.20047 (sha256 a21061c8…), §4 p.18 (PDF p.21)

import Mathlib
import Definitions.Def_ParallelHAC_HACRun

namespace ParallelHAC

/-- `X_i`, the cluster of `C_i` containing the fixed point `x₀` just before the `i`-th merge
(§4, p.18).
Source: arXiv:2507.20047 (sha256 a21061c8…), §4, p.18.

**Formalization Note.** Written as the union of the members of `C_i` that contain `x₀`; for a run
(whose clusterings partition `P`) and `x₀ ∈ P` this union is the unique such cluster. -/
def HACRun.clusterOf {V : Type*} [DecidableEq V] {P : Finset V}
    {d : Finset V → Finset V → ℝ} {c : ℝ} (R : HACRun P d c) (x₀ : V) (i : ℕ) : Finset V :=
  ((R.C i).filter (fun S => x₀ ∈ S)).sup id

/-- `X_i` participates in the `i`-th merge: `X_i ∈ {A_i, B_i}` (§4, p.18).
Source: arXiv:2507.20047 (sha256 a21061c8…), p.18. -/
def HACRun.Participates {V : Type*} [DecidableEq V] {P : Finset V}
    {d : Finset V → Finset V → ℝ} {c : ℝ} (R : HACRun P d c) (x₀ : V) (i : ℕ) : Prop :=
  R.clusterOf x₀ i = R.A i ∨ R.clusterOf x₀ i = R.B i

instance {V : Type*} [DecidableEq V] {P : Finset V} {d : Finset V → Finset V → ℝ} {c : ℝ}
    (R : HACRun P d c) (x₀ : V) : DecidablePred (R.Participates x₀) := fun i => by
  unfold HACRun.Participates; infer_instance

/-- `X̄_i`, the cluster with which `X_i` merges: the one element of `{A_i, B_i} \ {X_i}` (§4,
p.18). Only meaningful when `X_i` participates in the `i`-th merge.
Source: arXiv:2507.20047 (sha256 a21061c8…), p.18. -/
def HACRun.partner {V : Type*} [DecidableEq V] {P : Finset V}
    {d : Finset V → Finset V → ℝ} {c : ℝ} (R : HACRun P d c) (x₀ : V) (i : ℕ) : Finset V :=
  if R.clusterOf x₀ i = R.A i then R.B i else R.A i

end ParallelHAC


