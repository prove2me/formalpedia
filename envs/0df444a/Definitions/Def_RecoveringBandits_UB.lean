-- Prove2me | Definitions.Def_RecoveringBandits_UB
-- name    : RecoveringBandits_UB
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:55:25.915493+00:00
-- url     : https://prove2.me/theorems/a3a0fd42-adef-431b-8459-a05bf1a53319
-- title:
--   The upper bound $\mathrm{UB}_R[K]$ of problem (3) and its optimal solutions
-- statement:
--   Problem (3) is
--
--   $$\max_{x\in[0,1]^N}\ T\sum_{i=1}^N F_i(x_i)\quad\text{s.t.}\quad\sum_{i=1}^N x_i\le K,$$
--
--   and its optimal value is written $\mathrm{UB}_R[K]\cdot T$. So
--
--   $$\mathrm{UB}_R[K]=\sup\Big\{\sum_{i=1}^N F_i(x_i)\ :\ x\in[0,1]^N,\ \sum_i x_i\le K\Big\}.$$
--
--   An **optimal solution** of (3) is a feasible $x$ whose objective is at least that of every feasible point. $\mathrm{UB}_R[K]$ is the long-run benchmark that the purely periodic policies are compared against.
--
--   **Formalization Note** For an admissible instance the set is nonempty ($x=0$) and bounded above, so the supremum is real. Optimality is stated by comparison with every feasible point, without reference to the supremum.
-- source:
--   Simchi-Levi–Zheng–Zhu, Offline Planning and Online Learning under Recovering Rewards, arXiv:2106.14813v2, §4.1, problem (3), p.11

import Mathlib
import Definitions.Def_RecoveringBandits_F

namespace RecoveringBandits

/-- **Feasible points of problem (3)** (arXiv:2106.14813v2, §4.1, (3), p.11): `x ∈ [0, 1]^N`
with `∑_i x_i ≤ K`. -/
def Feasible3 {N : ℕ} (K : ℕ) (x : Fin N → ℝ) : Prop :=
  (∀ i, x i ∈ Set.Icc (0 : ℝ) 1) ∧ ∑ i, x i ≤ K

/-- **`UB_R[K]`** (arXiv:2106.14813v2, §4.1, (3), p.11): problem (3) is
`max_{x ∈ [0,1]^N} T ∑_i F_i(x_i)` s.t. `∑_i x_i ≤ K`, and the paper denotes its objective value
by `UB_R[K] · T`. So `UB_R[K]` is the supremum of `∑_i F_i(x_i)` over the feasible points.

**Formalization Note.** For an admissible instance every `F_i` takes values in `[0, Rmax]` on
`[0, 1]`, so the set is bounded above, and it is nonempty (`x = 0` is feasible), so `sSup` is the
real supremum (attained, by Lemma 2). -/
noncomputable def UB {N : ℕ} (R : Fin N → ℕ → ℝ) (K : ℕ) : ℝ :=
  sSup {v : ℝ | ∃ x : Fin N → ℝ, Feasible3 K x ∧ v = ∑ i, F (R i) (x i)}

/-- **An optimal solution of problem (3)** (arXiv:2106.14813v2, §4.1, (3), p.11): a feasible
point whose objective `∑_i F_i(x_i)` is at least that of every feasible point. (Stated by
comparison with every feasible point, not by equality with `UB`, so it carries no `sSup`
convention.) -/
def IsOpt3 {N : ℕ} (R : Fin N → ℕ → ℝ) (K : ℕ) (x : Fin N → ℝ) : Prop :=
  Feasible3 K x ∧ ∀ y : Fin N → ℝ, Feasible3 K y → ∑ i, F (R i) (y i) ≤ ∑ i, F (R i) (x i)

end RecoveringBandits


