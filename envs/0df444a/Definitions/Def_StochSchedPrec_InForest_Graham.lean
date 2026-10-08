-- Prove2me | Definitions.Def_StochSchedPrec_InForest_Graham
-- name    : StochSchedPrec_InForest_Graham
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T08:44:24.350822+00:00
-- url     : https://prove2.me/theorems/90dd15e2-2a82-4e90-87de-60f9e7912dcc
-- title:
--   §1, p. 790 and Definitions 2.2–2.3, p. 792 — Graham's list scheduling, availability, critical predecessors and critical chains
-- statement:
--   Fix a realization $p\ge 0$ of the processing times and a schedule $S$, with completion times $C_j=S_j+p_j$; there are no release dates.
--
--   **Availability.** Job $j$ is *available* at time $t\ge 0$ if all predecessors of $j$ are completed by $t$ (p. 790). The earliest such time is
--   $$r_j(p)=\max\Big(\{0\}\cup\{C_i: i \text{ a predecessor of } j\}\Big).$$
--
--   **Graham's list scheduling** (§1, p. 790): "Iterating over decision times, it greedily starts as many available jobs as possible, always in the order of the list $L$." A schedule $S$ is the Graham schedule for the list $L$ on $m$ machines when
--   1. $S$ is feasible;
--   2. (greedy) if a job $j$ is available at $t$ but has not started ($t<S_j$), then all $m$ machines are busy at $t$;
--   3. (list order) if a job $l$ starts at $t=S_l$ while a job $j$ that starts later is already available at $t$, then $l$ precedes $j$ in $L$;
--   4. (decision times) every job starts at time $0$ or at the completion time of another job.
--
--   **Critical predecessors** (Definition 2.2, with $r_j=0$). A critical predecessor of $j$ is a predecessor $i$ of $j$ with $C_i>0$ and $C_i$ maximal among all predecessors of $j$. A *selector* chooses for each job $j$ either one critical predecessor or "none" when $j$ has none; this is the paper's "arbitrary but fixed tie-breaking rule" (p. 793).
--
--   **Critical chains** (Definition 2.3, with $r_j=0$). For a selector, the length $\ell_j(p)$ of the critical chain for $j$ is defined backwards recursively: $\ell_j(p)=p_j$ if $j$ has no critical predecessor, and $\ell_j(p)=p_j+\ell_k(p)$ where $k$ is the selected critical predecessor of $j$ otherwise.
--
--   These objects enter Lemma 4.3, Lemma 4.4 and the critical-chain lower bound.
--
--   **Formalization Note** Graham's algorithm is characterized by the four rules above rather than simulated; every statement of the mission quantifies over all schedules satisfying the rules. Predecessors are path predecessors (transitive closure of $A$). The recursion for $\ell_j$ is run for $|V|$ steps; for a selector that chooses predecessors and acyclic precedence constraints the chain visits distinct jobs, so it always ends before the step bound and the value is that of Definition 2.3.
-- source:
--   Skutella and Uetz, Stochastic machine scheduling with precedence constraints, SIAM J. Comput. 34(4) (2005) 788–802, p. 790 (Graham's list scheduling, availability), p. 792 (Definitions 2.2, 2.3), p. 793 (tie-breaking, r_j(p))

import Mathlib
import Definitions.Def_StochSchedPrec_InForest_Model

namespace StochSchedPrec.InForest

variable {V : Type*}

/-- Job `j` is available at time `t` in the schedule `S` for the realization `p` (p. 790,
without release dates): `t ≥ 0` and every (path) predecessor `i` of `j` is completed by `t`,
i.e. `S i + p i ≤ t`. -/
def IsAvailable (A : V → V → Prop) (p S : V → ℝ) (j : V) (t : ℝ) : Prop :=
  0 ≤ t ∧ ∀ i, Relation.TransGen A i j → S i + p i ≤ t

/-- `S` is the schedule produced by Graham's list scheduling with priority list `L` on `m`
machines for the realization `p` (§1, p. 790), characterized by its rules:
1. `S` is a feasible schedule;
2. greedy: if a job `j` is available at time `t` and has not started (`t < S j`), then all `m`
   machines are busy at `t` (at least `m` jobs `k` with `S k ≤ t < S k + p k`);
3. list order: if a job `l` starts at time `t = S l` while a job `j` that starts later is
   already available at `t`, then `l` precedes `j` in `L`;
4. decision times: every job starts at time `0` or at the completion time of another job. -/
def IsGraham [Fintype V] (A : V → V → Prop) (m : ℕ) (L : Fin (Fintype.card V) ≃ V)
    (p S : V → ℝ) : Prop :=
  IsFeasibleSchedule A m p S ∧
  (∀ (j : V) (t : ℝ), IsAvailable A p S j t → t < S j →
    m ≤ (Finset.univ.filter fun k => S k ≤ t ∧ t < S k + p k).card) ∧
  (∀ l j : V, IsAvailable A p S j (S l) → S l < S j → L.symm l < L.symm j) ∧
  (∀ j : V, S j = 0 ∨ ∃ k, k ≠ j ∧ S j = S k + p k)

open Classical in
/-- `r_j(p)` (p. 793, without release dates): the earliest time at which job `j` is available
in the schedule `S`, namely the maximum of `0` and of the completion times `S i + p i` of all
(path) predecessors `i` of `j`. -/
noncomputable def availTime (A : V → V → Prop) [Fintype V] (p S : V → ℝ) (j : V) : ℝ :=
  (Finset.univ.filter fun i => Relation.TransGen A i j).fold max 0 (fun i => S i + p i)

/-- `crit` selects critical predecessors in the schedule `S` for the realization `p`
(Definition 2.2, p. 792, with release dates `r_j = 0`): `crit j = some i` only if `i` is a
(path) predecessor of `j` with `C_i > 0` and `C_i` maximal among all predecessors of `j`
(`C_i = S i + p i`), and `crit j = none` only if `j` has no such predecessor. Ties are broken
arbitrarily but fixed by the choice of `crit`. -/
def IsCritSelector (A : V → V → Prop) (p S : V → ℝ) (crit : V → Option V) : Prop :=
  ∀ j,
    (∀ i, crit j = some i →
      Relation.TransGen A i j ∧ 0 < S i + p i ∧
        ∀ i', Relation.TransGen A i' j → S i' + p i' ≤ S i + p i) ∧
    (crit j = none →
      ¬ ∃ i, Relation.TransGen A i j ∧ 0 < S i + p i ∧
        ∀ i', Relation.TransGen A i' j → S i' + p i' ≤ S i + p i)

/-- The backwards recursion of Definition 2.3 (p. 792) with release dates `r_j = 0`, run for
at most `n` steps: `ℓ_j = p_j` if `crit j = none`, and `ℓ_j = p_j + ℓ_i` if `crit j = some i`. -/
noncomputable def chainLenAux (crit : V → Option V) (p : V → ℝ) : ℕ → V → ℝ
  | 0, j => p j
  | n + 1, j =>
    match crit j with
    | none => p j
    | some i => p j + chainLenAux crit p n i

/-- The length `ℓ_j(p)` of the critical chain for job `j` (Definition 2.3, p. 792, release dates
`r_j = 0`) determined by the critical-predecessor selector `crit`. For a selector satisfying
`IsCritSelector` with acyclic precedence constraints, each step moves to a strict predecessor,
so the chain has at most `card V` jobs and the recursion with `card V` steps never runs out. -/
noncomputable def chainLen [Fintype V] (crit : V → Option V) (p : V → ℝ) (j : V) : ℝ :=
  chainLenAux crit p (Fintype.card V) j

end StochSchedPrec.InForest


