-- Prove2me | Definitions.Def_SchedComplexity_OneMachine_Constructions
-- name    : SchedComplexity_OneMachine_Constructions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:41:00.666983+00:00
-- url     : https://prove2.me/theorems/c36e3310-0aa3-4d01-888b-328124df9192
-- title:
--   The instances and thresholds of reductions (b), (c), (e), (f) of Theorem 4
-- statement:
--   The constructions of Theorem 4(b), (c), (e), (f) of Brucker, Lenstra and Rinnooy Kan, from KNAPSACK data $a_1,\dots,a_t,b$ with $T=\{1,\dots,t\}$ and $A=\sum_{j\in T}a_j$.
--
--   1. Reductions (c) and (f) (p. 17): $n=t+1$ jobs; for $j\in T$: $r_j=0$, $p_{j1}=a_j$, $d_j=A+1$; for the last job: $r_n=b$, $p_{n1}=1$, $d_n=b+1$; threshold $y=0$. All weights are $1$.
--   2. Reduction (e) (p. 19): $n=t$ jobs with $p_{j1}=w_j=a_j$, $d_j=b$ $(j\in T)$, all release dates $0$; threshold $y_E=A-b$.
--   3. Reduction (b) (p. 19): $n=t+1$ jobs; for $j\in T$: $p_{j1}=w_j=a_j$, $d_j=A+1$; for the last job $p_{n1}=1$, $w_n=0$, $d_n=b+1$; all release dates $0$; threshold
--   $$y_B=\sum_{j,k\in T,\ j\le k}a_ja_k+A-b .$$
--
--   The mission's milestones state, for each construction, that KNAPSACK has a solution iff the constructed instance has a feasible schedule of value at most the threshold.
--
--   **Formalization Note** The last job $J_n$ is index $t$ (`Fin.last`), the KNAPSACK jobs are indices $0,\dots,t-1$. Reduction (c) does not specify weights; the shared construction sets them to $1$, as (f) needs. The thresholds use natural-number subtraction, which is the paper's value under the proof's assumption $0<b<A$ (p. 16).
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 17 (Theorem 4(c),(f)) and p. 19 (Theorem 4(e),(b))

import Mathlib
import Definitions.Def_SchedComplexity_OneMachine_Model

namespace SchedComplexity.OneMachine

/-- The instance of reductions (c) and (f) of Theorem 4 (Brucker, Lenstra & Rinnooy Kan, Report
BW 43/75, p. 17), built from the KNAPSACK data `a = [a_1, …, a_t]`, `b`, with `A = ∑_{j∈T} a_j`:
`n = t + 1` jobs; for `j ∈ T` (indices `0, …, t-1`): `r_j = 0`, `p_{j1} = a_j`, `d_j = A + 1`;
for the last job `J_n` (index `t`): `r_n = b`, `p_{n1} = 1`, `d_n = b + 1`. All weights are `1`
(as (f) requires; (c) does not use weights). The threshold is `y = 0`. -/
def instCF (a : List ℕ) (b : ℕ) : Instance where
  n := a.length + 1
  p := Fin.lastCases 1 (fun j => a.get j)
  w := fun _ => 1
  r := Fin.lastCases b (fun _ => 0)
  d := Fin.lastCases (b + 1) (fun _ => a.sum + 1)

/-- The instance of reduction (e) of Theorem 4 (p. 19): `n = t` jobs, `p_{j1} = w_j = a_j`,
`d_j = b`, `r_j = 0` for `j ∈ T`. -/
def instE (a : List ℕ) (b : ℕ) : Instance where
  n := a.length
  p := fun j => a.get j
  w := fun j => a.get j
  r := fun _ => 0
  d := fun _ => b

/-- The threshold `y = A - b` of reduction (e) (p. 19), with `A = ∑_{j∈T} a_j`. Natural-number
subtraction: it is the paper's value whenever `b ≤ A` (the proof assumes `0 < b < A`). -/
def yE (a : List ℕ) (b : ℕ) : ℕ := a.sum - b

/-- The instance of reduction (b) of Theorem 4 (p. 19): `n = t + 1` jobs; for `j ∈ T`:
`p_{j1} = w_j = a_j`, `d_j = A + 1`; for `J_n`: `p_{n1} = 1`, `w_n = 0`, `d_n = b + 1`; all
release dates `0`. -/
def instB (a : List ℕ) (b : ℕ) : Instance where
  n := a.length + 1
  p := Fin.lastCases 1 (fun j => a.get j)
  w := Fin.lastCases 0 (fun j => a.get j)
  r := fun _ => 0
  d := Fin.lastCases (b + 1) (fun _ => a.sum + 1)

/-- The threshold `y = ∑_{j,k∈T, j≤k} a_j a_k + A - b` of reduction (b) (p. 19); the double sum
runs over pairs of indices `j ≤ k`. Natural-number subtraction: it is the paper's value whenever
`b ≤ A + ∑_{j≤k} a_j a_k`, in particular under the proof's assumption `0 < b < A`. -/
def yB (a : List ℕ) (b : ℕ) : ℕ :=
  (∑ k : Fin a.length, ∑ j ∈ Finset.Iic k, a.get j * a.get k) + a.sum - b

end SchedComplexity.OneMachine


