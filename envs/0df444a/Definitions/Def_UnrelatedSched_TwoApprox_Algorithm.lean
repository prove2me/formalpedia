-- Prove2me | Definitions.Def_UnrelatedSched_TwoApprox_Algorithm
-- name    : UnrelatedSched_TwoApprox_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T14:16:43.075986+00:00
-- url     : https://prove2.me/theorems/ec4e5393-77e5-473f-b59e-217bac267e6f
-- title:
--   The greedy schedule, ρ-relaxed decision procedures, the binary search of Lemma 1, and the LP rounding procedure (Section 3)
-- statement:
--   Fix a matrix $P=(p_{ij})$ of processing times in $\mathbb N$ for $m\ge 1$ machines and $n$ jobs. All makespans of schedules for $P$ are integers.
--
--   A **decision procedure** $D$ answers, for each deadline $d\in\mathbb N$, either 'no' or 'almost' together with a schedule. It is **$\rho$-relaxed** if, on input $(P,d)$,
--   1. it either outputs 'no' or produces a schedule with makespan at most $\rho d$, and
--   2. if the output is 'no', then there is no schedule with makespan at most $d$.
--
--   The **greedy schedule** assigns each job to a machine on which it runs fastest, i.e. to a machine minimizing $p_{ij}$ (the smallest such index on ties). The **binary search of Lemma 1** built from $D$ starts from the greedy schedule, with upper bound $u$ equal to its makespan $t$ and lower bound $l=\lceil t/m\rceil$. While $l<u$ it sets
--   $$d=\Big\lfloor \frac{u+l}{2}\Big\rfloor$$
--   and queries $D$ at $d$: on 'almost' with a schedule $\sigma$ it resets $u$ to $d$ and stores $\sigma$ if its makespan is smaller than that of the best schedule stored so far; on 'no' it resets $l$ to $d+1$. When $l=u$ it outputs the best schedule found (the greedy schedule counts as found).
--
--   A **vertex selector** $V$ returns, for each $d\in\mathbb N$, a vertex of (LP) with $d_1=\dots=d_m=t=d$ when that LP is feasible, and 'none' exactly when it is infeasible; it models the LP solver, whose choice of vertex is arbitrary. The **LP rounding procedure driven by $V$** is any decision procedure $D$ that answers 'no' at $d$ exactly when $V$ finds no vertex, and otherwise answers 'almost' with a schedule $\sigma$ that is a rounding of the chosen vertex $\tilde x$: $\sigma$ is supported on $\tilde x$ and is a 0-1 solution of (IP) with $d_1=\dots=d_m=t=d$, i.e. every machine load is at most $2d$.
--
--   These objects are the algorithmic side of the mission: Lemma 1 analyses the binary search, and Theorem 2 applies it to the LP rounding procedure.
--
--   **Formalization Note** A decision procedure is a function `ℕ → Option (Fin n → Fin m)` (`none` = 'no'). The paper's lower bound $t/m$ is rounded up to $\lceil t/m\rceil$, which is still a lower bound on the optimum because the optimum is an integer. The search compares makespans in $\mathbb N$ (`natMakespan`, whose cast is the published `makespan`); the output is the best schedule found, the earlier one on ties. Termination is by recursion on $u-l$. The greedy schedule needs $m\ge 1$, so the algorithm takes a proof of $0<m$. Running time is not modelled.
-- source:
--   Lenstra, Shmoys, Tardos, Approximation algorithms for scheduling unrelated parallel machines, CWI Report OS-R8714 (1987), p. 5, Section 3 (ρ-relaxed decision procedure) and proof of Lemma 1 (binary search); pp. 5–6 (the LP procedure)

import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_TwoApprox_DeadlineLP

namespace UnrelatedSched.TwoApprox

open MatousekLP.Scheduling

/-- The load of machine `i` under `σ`, computed in `ℕ`: `∑_{j : σ(j) = i} p_ij`. -/
def natLoad {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (σ : Fin n → Fin m) (i : Fin m) : ℕ :=
  ∑ j ∈ Finset.univ.filter (fun j => σ j = i), P i j

/-- The makespan of `σ` computed in `ℕ`, the largest machine load (`0` when `m = 0`). Its cast to `ℝ`
is the published `makespan (realTimes P) σ`. The binary search compares and bounds makespans with it,
because all of them are integers. -/
def natMakespan {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (σ : Fin n → Fin m) : ℕ :=
  Finset.univ.sup fun i => natLoad P σ i

/-- A machine on which job `j` runs fastest, i.e. minimizing `p_ij` over `i`; ties are broken by the
smallest machine index. Needs `m > 0`. -/
noncomputable def fastestMachine {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (hm : 0 < m)
    (j : Fin n) : Fin m :=
  (Finset.univ.filter fun i => ∀ i', P i j ≤ P i' j).min' (by
    obtain ⟨i, -, hi⟩ :=
      Finset.univ.exists_min_image (fun i => P i j) ⟨⟨0, hm⟩, Finset.mem_univ _⟩
    exact ⟨i, by simpa using hi⟩)

/-- The greedy schedule of the proof of Lemma 1 (p. 5): each job is assigned to the machine on which
it runs fastest. -/
noncomputable def greedySchedule {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (hm : 0 < m) :
    Fin n → Fin m :=
  fastestMachine P hm

/-- A decision procedure for a fixed matrix `P`: on deadline `d` it answers `none` ('no') or
`some σ` ('almost', together with the schedule `σ`). -/
abbrev DecisionProcedure (m n : ℕ) : Type := ℕ → Option (Fin n → Fin m)

/-- A `ρ`-relaxed decision procedure (§3, p. 5): on input `(P, d)`, (1) it either outputs 'no' or
produces a schedule with makespan at most `ρ d`, and (2) if the output is 'no', then there is no
schedule with makespan at most `d`. -/
def IsRelaxedDecisionProcedure {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (ρ : ℝ)
    (D : DecisionProcedure m n) : Prop :=
  ∀ d : ℕ, (∀ σ, D d = some σ → makespan (realTimes P) σ ≤ ρ * d) ∧
    (D d = none → ∀ τ : Fin n → Fin m, (d : ℝ) < makespan (realTimes P) τ)

/-- The main loop of the binary search of Lemma 1 (p. 5), on lower bound `l`, upper bound `u` and the
best schedule `best` found so far. While `l < u` it sets `d = ⌊(u + l)/2⌋` and queries `D d`: on
'almost' with `σ` it resets `u` to `d` and keeps whichever of `σ` and `best` has the smaller makespan
(the earlier one on a tie); on 'no' it resets `l` to `d + 1`. When `l ≥ u` it outputs `best`. -/
noncomputable def searchLoop {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (D : DecisionProcedure m n)
    (l u : ℕ) (best : Fin n → Fin m) : Fin n → Fin m :=
  if _h : l < u then
    match D ((u + l) / 2) with
    | some σ =>
        searchLoop P D l ((u + l) / 2)
          (if natMakespan P σ < natMakespan P best then σ else best)
    | none => searchLoop P D ((u + l) / 2 + 1) u best
  else best
termination_by u - l
decreasing_by all_goals omega

/-- The ρ-approximation algorithm of Lemma 1 (p. 5) built from a decision procedure `D`. It starts
from the greedy schedule, whose makespan `t` is the initial upper bound `u`; the initial lower bound
is `⌈t/m⌉` (the paper's `t/m`, rounded up because every makespan is an integer). It then runs the
binary search `searchLoop` and outputs the best schedule found, the greedy one included. -/
noncomputable def binarySearch {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ) (hm : 0 < m)
    (D : DecisionProcedure m n) : Fin n → Fin m :=
  let g := greedySchedule P hm
  let u₀ := natMakespan P g
  searchLoop P D ⌈(u₀ : ℚ) / m⌉₊ u₀ g

/-- A vertex selector for `P`: for each deadline `d`, it returns a vertex of (LP) with
`d_1 = ⋯ = d_m = t = d` if that LP is feasible, and `none` exactly when it is infeasible. It models
the LP solver of §3 (p. 5), whose choice of vertex the analysis does not control. -/
def IsVertexSelector {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ)
    (V : ℕ → Option (Matrix (Fin m) (Fin n) ℝ)) : Prop :=
  ∀ d : ℕ, (∀ x, V d = some x → IsLPVertex P (fun _ => (d : ℝ)) d x) ∧
    (V d = none → LPPolytope P (fun _ => (d : ℝ)) d = ∅)

/-- `D` is the decision procedure of §3 (pp. 5–6) driven by the vertex selector `V`: on deadline `d`
it answers 'no' exactly when (LP) with `d_1 = ⋯ = d_m = t = d` has no vertex, and otherwise it answers
'almost' with a rounding of the chosen vertex `x̃ = V d`, i.e. a 0-1 solution of (IP) (loads at most
`d + d`) supported on `x̃`. -/
def IsLPRoundingProcedure {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ)
    (V : ℕ → Option (Matrix (Fin m) (Fin n) ℝ)) (D : DecisionProcedure m n) : Prop :=
  ∀ d : ℕ, (D d = none ↔ V d = none) ∧
    ∀ σ, D d = some σ → ∃ x, V d = some x ∧ SupportedOn x σ ∧
      IPFeasible P (fun _ => (d : ℝ)) d σ

end UnrelatedSched.TwoApprox


