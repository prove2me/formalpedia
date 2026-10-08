-- Prove2me | Definitions.Def_SchedComplexity_Partition_Constructions
-- name    : SchedComplexity_Partition_Constructions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T21:46:58.408656+00:00
-- url     : https://prove2.me/theorems/ed530c10-f840-4068-90c8-ecacea716e02
-- title:
--   The constructions of Theorem 3: $A$, $p_{j1}=a_j$, $y=\tfrac12A$; $p_{j1}=w_j=a_j$, $y=\sum_{j\le k}a_ja_k-\tfrac14A^2$; $k(S)$
-- statement:
--   The data of the two reductions in the proof of Theorem 3 of Brucker, Lenstra & Rinnooy Kan, for a PARTITION instance $a_1,\dots,a_t$ with $T=\{1,\dots,t\}$:
--
--   1. $A = \sum_{j\in T} a_j$.
--   2. Construction (a): $n=t$ jobs with $p_{j1}=a_j$ $(j\in T)$ and threshold $y=\tfrac12 A$.
--   3. Construction (b): $n=t$ jobs with $p_{j1}=w_j=a_j$ $(j\in T)$ and threshold
--   $$y = \sum_{j,k\in T,\ j\le k} a_ja_k - \tfrac14 A^2,$$
--   where the sum runs over index pairs $j\le k$, the diagonal $j=k$ included.
--   4. For $S\subseteq T$,
--   $$k(S) = \sum_{j,k\in S,\ j\le k} a_ja_k + \sum_{j,k\in T-S,\ j\le k} a_ja_k,$$
--   the value of $\sum w_jC_j$ in construction (b) when the jobs of $S$ are on $M_1$, those of $T-S$ on $M_2$, and each machine works without idle time from time $0$. In particular $k(T)=\sum_{j,k\in T,\ j\le k}a_ja_k$.
--
--   These are the objects about which the milestones of Theorem 3 are stated.
--
--   **Formalization Note** Indices are 0-based. Both thresholds are rational as printed and are defined as real numbers; the integer threshold used in the reduction of the goal theorem is their floor. The paper introduces $k(S)$ as the schedule value; here it is defined by the closed form above, and that it equals the schedule value is the milestone `theorem_3b_value_eq_k`.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 15, proof of Theorem 3

import Mathlib

namespace SchedComplexity.Partition

/-- `A = Σ_{j ∈ T} a_j` (proof of Theorem 3, p. 15), for the PARTITION data `a_1, …, a_t`
(the list `a`, indices `j < t`). -/
def totalA (a : List ℕ) : ℕ :=
  ∑ j : Fin a.length, a.get j

/-- Construction (a) of Theorem 3 (p. 15): `n = t` jobs with `p_{j1} = a_j`. -/
def procA (a : List ℕ) : Fin a.length → ℕ :=
  fun j => a.get j

/-- The threshold of construction (a): `y = ½A`, a rational number (a real here). -/
noncomputable def yA (a : List ℕ) : ℝ :=
  (totalA a : ℝ) / 2

/-- Construction (b) of Theorem 3 (p. 15): `n = t` jobs with `p_{j1} = w_j = a_j`; this is the
common vector of processing times and weights. -/
def procB (a : List ℕ) : Fin a.length → ℕ :=
  fun j => a.get j

/-- `Σ_{j,k ∈ T, j ≤ k} a_j a_k`: the sum over index pairs `j ≤ k`, the diagonal `j = k`
included. -/
def pairSum (a : List ℕ) : ℕ :=
  ∑ j : Fin a.length, ∑ k : Fin a.length, if j ≤ k then a.get j * a.get k else 0

/-- The threshold of construction (b): `y = Σ_{j,k ∈ T, j ≤ k} a_j a_k − ¼A²`, a rational number
(a real here). -/
noncomputable def yB (a : List ℕ) : ℝ :=
  (pairSum a : ℝ) - (totalA a : ℝ) ^ 2 / 4

/-- `k(S)` (proof of Theorem 3(b), p. 15): the value of `Σ w_j C_j` in construction (b) when the
jobs of `S` are on `M_1` and those of `T − S` on `M_2`, each machine working without idle time
from `0`, in closed form: `Σ_{j,k ∈ S, j ≤ k} a_j a_k + Σ_{j,k ∈ T−S, j ≤ k} a_j a_k`. That this
closed form is the schedule value is the content of the milestone `theorem_3b_value_eq_k`. -/
def kVal (a : List ℕ) (S : Finset (Fin a.length)) : ℕ :=
  (∑ j ∈ S, ∑ k ∈ S, if j ≤ k then a.get j * a.get k else 0) +
    ∑ j ∈ Sᶜ, ∑ k ∈ Sᶜ, if j ≤ k then a.get j * a.get k else 0

end SchedComplexity.Partition


