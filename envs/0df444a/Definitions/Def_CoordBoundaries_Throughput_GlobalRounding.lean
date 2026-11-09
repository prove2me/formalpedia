-- Prove2me | Definitions.Def_CoordBoundaries_Throughput_GlobalRounding
-- name    : CoordBoundaries_Throughput_GlobalRounding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:43:47.287203+00:00
-- url     : https://prove2.me/theorems/8177458a-6ace-4892-ae6a-4eb761185463
-- title:
--   The complementary global-job rounding of Appendix B: assignment law, long jobs, load tests and placement
-- statement:
--   Fix a configuration solution and $\eta=1/q$. For machine $i$, $y_{j,B,i}=\sum_C x_{B,C}\,\mathbf 1\{\text{the stored schedule of }C\text{ places }j\text{ on machine }i\}$. Independently for each global job $j$, assign $j$ to the pair $(B,i)$ with probability $(1-2\eta)y_{j,B,i}$ and leave it unassigned with the remaining probability; local jobs are not used.
--
--   Write $I_{j,B}=B\cap[r_j,d_j)$. An assignment is **long** if $p_j>\eta^4|I_{j,B}|$; long assignments are discarded. For $B=[s,t)$ and machine $i$, let $J_{B,i}$ be the short jobs assigned to $(B,i)$. Retain $j\in J_{B,i}$ exactly when the applicable tests hold on the pre-deletion set $J_{B,i}$:
--   $$\sum_{k\in J_{B,i}}p_k\le t-s,\qquad \sum_{k\in J_{B,i},\,d_k\le d_j}p_k\le d_j-s\ \text{ if } s<d_j<t,\qquad \sum_{k\in J_{B,i},\,r_k\ge r_j}p_k\le t-r_j\ \text{ if } s<r_j<t.$$
--   Survivors with $s<d_j<t$ are placed from $s$ in increasing deadline order, survivors with $s<r_j<t$ in increasing release order in a suffix ending at $t$, and the remaining survivors in the gap. $A_{\mathrm{glob}}$ is the number of survivors.
--
--   **Formalization Note** Orders left free by the source (ties, the order inside the gap) are fixed by an arbitrary injective key on jobs; since each job lies in at most one group, one key realizes every choice.
-- source:
--   Tong and Xu, Coordinating Boundaries: Improved Approximation Algorithms for Unweighted Non-Preemptive Throughput Maximization, preprint of October 25, 2026 (STOC 2027 submission #141; source.pdf sha256 59f76539a5ee555f9e56603a067e9f858f38d003011e90b1716085348673687e), pp. 29–31, Appendix B (assignment, long jobs, load tests, placement)

import Mathlib
import Definitions.Def_CoordBoundaries_Throughput_Relaxation

open Classical

namespace CoordBoundaries.Throughput

/-! # Complementary global-job rounding (Tong–Xu, §4.5 and Appendix B, pp. 26, 29–31)

Independently for each global job `j`, assign it to at most one pair `(B, i)` (block, machine),
choosing `(B, i)` with probability `(1 − 2η) y_{j,B,i}`; local jobs are never assigned. Discard long
assignments (`p_j > η⁴ |I_{j,B}|`, `I_{j,B} = B ∩ [r_j, d_j)`). For each `(B, i)` with
`B = [s, t)`, let `J_{B,i}` be its short assigned jobs and retain `j ∈ J_{B,i}` exactly when the
applicable load tests hold on the pre-deletion `J_{B,i}`. Survivors are placed on machine `i` in
`B`: jobs with `s < d_j < t` in increasing deadline order from `s`, jobs with `s < r_j < t` in
increasing release order in a suffix ending at `t`, the remaining (spanning) jobs in the gap. Ties
and the order inside the gap are given by an arbitrary injective key `key : jobs → ℕ` (every job is
in at most one group, so one key realizes every choice). `A_glob` is the number of survivors. -/

/-- An assignment outcome: each job is unassigned or assigned to a (block, machine) pair. -/
abbrev Assign (I : Instance) (P : Partition I.T) := Fin I.n → Option (Fin P.len × Fin I.m)

namespace ConfigSol

variable {I : Instance} {P : Partition I.T} {K : ℕ} (s : ConfigSol I P K)

/-- `y_{j,B,i} = Σ_C x_{B,C} 1{the stored schedule for C places j on machine i}` (p. 29). -/
noncomputable def ymach (j : Fin I.n) (B : Fin P.len) (i : Fin I.m) : ℝ :=
  ∑ C ∈ P.configs K B, s.x B C * (if ∃ S : ℝ, s.store B C j = some (i, S) then 1 else 0)

/-- Probability that job `j` receives assignment `o` (p. 30). -/
noncomputable def asgProb (q : ℕ) (j : Fin I.n) : Option (Fin P.len × Fin I.m) → ℝ
  | none => 1 - (if P.IsGlobal j then (1 - 2 * eta q) * ∑ B, ∑ i, s.ymach j B i else 0)
  | some (B, i) => if P.IsGlobal j then (1 - 2 * eta q) * s.ymach j B i else 0

/-- Probability of an assignment outcome (independent across jobs). -/
noncomputable def asgLaw (q : ℕ) (α : Assign I P) : ℝ := ∏ j, s.asgProb q j (α j)

end ConfigSol

namespace Partition

variable {I : Instance} (P : Partition I.T)

/-- `|I_{j,B}|`, the length of `B ∩ [r_j, d_j)` (`0` if empty). -/
noncomputable def usableLen (j : Fin I.n) (B : Fin P.len) : ℝ :=
  max 0 ((min (P.hi B) (I.d j) : ℝ) - (max (P.lo B) (I.r j) : ℝ))

/-- `J_{B,i}`: the short jobs assigned to `(B, i)`. -/
noncomputable def shortAssigned (q : ℕ) (α : Assign I P) (B : Fin P.len) (i : Fin I.m) :
    Finset (Fin I.n) :=
  Finset.univ.filter fun j => α j = some (B, i) ∧ (I.p j : ℝ) ≤ eta q ^ 4 * P.usableLen j B

/-- The applicable load tests of `j` on the pre-deletion set `J = J_{B,i}`, `B = [s, t)` (p. 30). -/
def PassesTests (J : Finset (Fin I.n)) (B : Fin P.len) (j : Fin I.n) : Prop :=
  (∑ k ∈ J, I.p k ≤ P.hi B - P.lo B) ∧
  (P.lo B < I.d j → I.d j < P.hi B → ∑ k ∈ J.filter (fun k => I.d k ≤ I.d j), I.p k ≤ I.d j - P.lo B) ∧
  (P.lo B < I.r j → I.r j < P.hi B → ∑ k ∈ J.filter (fun k => I.r j ≤ I.r k), I.p k ≤ P.hi B - I.r j)

/-- The survivors `J′_{B,i}`. -/
noncomputable def survivors (q : ℕ) (α : Assign I P) (B : Fin P.len) (i : Fin I.m) :
    Finset (Fin I.n) :=
  (P.shortAssigned q α B i).filter (P.PassesTests (P.shortAssigned q α B i) B)

/-- Start time of a survivor `j ∈ J′` in block `B` (p. 31): deadline group from `s` in increasing
`(d_j, key j)` order; release group in a suffix ending at `t` in increasing `(r_j, key j)` order; the
remaining (spanning) jobs after the deadline group in increasing `key` order. -/
noncomputable def placeStart (key : Fin I.n → ℕ) (J' : Finset (Fin I.n)) (B : Fin P.len)
    (j : Fin I.n) : ℕ :=
  let G1 := J'.filter fun k => P.lo B < I.d k ∧ I.d k < P.hi B
  let G3 := J'.filter fun k => P.lo B < I.r k ∧ I.r k < P.hi B
  let G2 := (J' \ G1) \ G3
  if j ∈ G1 then
    P.lo B + ∑ k ∈ G1.filter (fun k => I.d k < I.d j ∨ (I.d k = I.d j ∧ key k < key j)), I.p k
  else if j ∈ G3 then
    P.hi B - ∑ k ∈ G3.filter (fun k => I.r j < I.r k ∨ (I.r k = I.r j ∧ key j ≤ key k)), I.p k
  else
    P.lo B + (∑ k ∈ G1, I.p k) +
      ∑ k ∈ G2.filter (fun k => key k < key j), I.p k

/-- The output schedule of the complementary rounding. -/
noncomputable def globSched (q : ℕ) (key : Fin I.n → ℕ) (α : Assign I P) : Sched I := fun j =>
  match α j with
  | none => none
  | some (B, i) =>
    if j ∈ P.survivors q α B i then some (i, (P.placeStart key (P.survivors q α B i) B j : ℝ))
    else none

/-- `A_glob`: the number of surviving jobs. -/
noncomputable def Aglob (q : ℕ) (α : Assign I P) : ℕ :=
  (Finset.univ.filter fun j => ∃ B i, α j = some (B, i) ∧ j ∈ P.survivors q α B i).card

end Partition

end CoordBoundaries.Throughput


