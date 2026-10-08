-- Prove2me | Definitions.Def_StochSchedPrec_CMNS_Algorithm
-- name    : StochSchedPrec_CMNS_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:53:42.318114+00:00
-- url     : https://prove2.me/theorems/2a8c1028-cc1c-4c33-acf1-f387f7950d79
-- title:
--   §2, pp. 793–794 — Algorithm CMNS (list scheduling with deliberate idle times and threshold βE[P_j]), its charging scheme, and O_j(p)
-- statement:
--   This file defines the schedule constructed by Algorithm CMNS of Skutella and Uetz (§2, p. 793), a list scheduling algorithm with deliberate idle times. The input is a priority list $L$, a parameter $\beta\ge0$, the expected processing times $\mu_j=\mathrm E[P_j]$ and a realization $p$.
--
--   The algorithm, verbatim: *Whenever a machine is idle and the first job in the residual list is available, the job is scheduled. Otherwise, if the first job is not available, the first available job $j$ in the residual list (if any) is deliberately delayed. If $j$ was deliberately delayed for an accumulated time of $\beta\mathrm E[P_j]$, it is scheduled out of order.* The *residual list* is the sublist of $L$ of the jobs not yet scheduled. Deliberate idle time accumulates $m'$ times faster when a job is deliberately delayed while $m'$ machines are idle, and is *charged* to the delayed job.
--
--   **Delayed job and charge.** At time $t$, after all decisions taken at $t$, the residual list consists of the jobs $i$ with $t<S_i$. A job $k$ is *deliberately delayed* at $t$ if the first job of the residual list is not available at $t$ and $k$ is the first available job of the residual list. The deliberate idle time charged to $k$ during $[0,t[$ is
--   $$\mathrm{charge}_k(t)=\int_0^t \big(m-\#\{\text{jobs in process at }s\}\big)\,\mathbf 1[k\text{ is deliberately delayed at }s]\,ds .$$
--
--   **A CMNS run.** A start-time vector $S$ is the schedule constructed by Algorithm CMNS for $p$ if it is feasible and the following hold.
--   1. The algorithm takes its decisions one job at a time in an order that is nondecreasing in time (several decisions may share an instant). At the decision for job $k$, at time $S_k$, the residual list consists of $k$ and the jobs decided after it; a machine is idle; $k$ is available (its predecessors were decided earlier and are complete by $S_k$); and either $k$ is the first job of the residual list, or the first job of the residual list is not available, $k$ is the first available job of the residual list, and $\mathrm{charge}_k(S_k)\ge\beta\mu_k$ ($k$ is scheduled out of order).
--   2. After all decisions at any time $t$: if a machine is idle, the first job of the residual list is not available; and if a machine is idle and $k$ is deliberately delayed, then $\mathrm{charge}_k(t)<\beta\mu_k$.
--
--   A *CMNS policy* is a map $\sigma$ such that $\sigma(p)$ is the CMNS schedule for every nonnegative realization $p$. Finally $O_j(p)\subseteq A_j$ is the set of jobs after $j$ in $L$ that are started before $j$ (out of order with respect to $j$).
--
--   The threshold $\beta\mathrm E[P_j]$, rather than $\beta p_j$, is what makes CMNS a nonanticipatory policy (footnote 2, p. 793); $\beta=0$ gives Graham's list scheduling.
--
--   **Formalization Note** The algorithm is characterized by its rules rather than simulated. The decision order `ord` makes the residual list well defined at instants where several jobs start at once, including jobs of length zero. Condition 2 expresses that the algorithm has nothing left to do at $t$; together with condition 1 it determines the run. The threshold vector `μ` is a parameter; the statements of the mission instantiate it with $\mu_j=\mathrm E[P_j]$ or keep it as an arbitrary nonnegative vector where the analysis is deterministic.
-- source:
--   Skutella and Uetz, Stochastic machine scheduling with precedence constraints, SIAM J. Comput. 34(4) (2005) 788–802, p. 793 (Algorithm CMNS, residual list, deliberate idle time, charging, footnote 2), pp. 793–794 (B_j, A_j, r_j(p), O_j(p))

import Mathlib
import Definitions.Def_StochSchedPrec_CMNS_Model

namespace StochSchedPrec.CMNS

open MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `k` is the first job of the list `L` among the jobs satisfying `q`. -/
def IsFirstWith (L : Fin (Fintype.card V) ≃ V) (q : V → Prop) (k : V) : Prop :=
  q k ∧ ∀ i, q i → L.symm k ≤ L.symm i

/-- Job `k` is deliberately delayed at time `t` in the schedule `S` (§2, p. 793): after all
decisions taken at `t`, the residual list is the set of jobs with `t < S i`; its first job is not
available, and `k` is the first available job of the residual list. -/
def IsDelayed (A : V → V → Prop) (r : V → ℝ) (L : Fin (Fintype.card V) ≃ V) (p S : V → ℝ)
    (k : V) (t : ℝ) : Prop :=
  (∃ i, IsFirstWith L (fun i => t < S i) i ∧ ¬ avail A r p S i t) ∧
    IsFirstWith L (fun i => t < S i ∧ avail A r p S i t) k

open Classical in
/-- The deliberate idle time charged to job `k` during `[0, t)` (§2, p. 793): while `k` is
deliberately delayed and `m'` machines are idle, deliberate idle time accumulates at rate `m'`
and is charged to `k`. -/
noncomputable def charge (m : ℕ) (A : V → V → Prop) (r : V → ℝ) (L : Fin (Fintype.card V) ≃ V)
    (p S : V → ℝ) (k : V) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, if IsDelayed A r L p S k s then ((m : ℝ) - (busy p S s : ℝ)) else 0

/-- Availability of job `i` at the moment the algorithm takes its decision for job `k` (at time
`S k`), when the jobs decided so far are those that precede `k` in the decision order `ord`:
`i` is released by `S k` and every predecessor of `i` has been decided earlier and has completed
by `S k`. -/
def AvailAtDecision (A : V → V → Prop) (r p S : V → ℝ) (ord : Fin (Fintype.card V) ≃ V)
    (k i : V) : Prop :=
  r i ≤ S k ∧ ∀ z, Relation.TransGen A z i → ord.symm z < ord.symm k ∧ S z + p z ≤ S k

/-- `S` is the schedule constructed by Algorithm CMNS (§2, p. 793) with priority list `L`,
parameter `β` and thresholds `β μ_j` (`μ_j = E[P_j]`) for the realization `p`, on `m` machines.

The algorithm takes its decisions one job at a time, in an order `ord` that is nondecreasing in
time (several decisions may be taken at the same instant). At its decision for job `k`, at time
`S k`, the residual list consists of `k` and the jobs decided after it; a machine is idle; `k` is
available; and either `k` is the first job of the residual list, or the first job of the residual
list is not available, `k` is the first available job of the residual list, and the deliberate
idle time charged to `k` has reached `β μ_k` (`k` is scheduled out of order).

After all decisions at any time `t`, the algorithm has nothing left to do: if a machine is idle,
the first job of the residual list is not available, and a deliberately delayed job has been
charged less than `β μ_k`. -/
def IsCMNSRun (m : ℕ) (A : V → V → Prop) (r : V → ℝ) (L : Fin (Fintype.card V) ≃ V)
    (β : ℝ) (μ : V → ℝ) (p S : V → ℝ) : Prop :=
  IsFeasible m A r p S ∧
  (∃ ord : Fin (Fintype.card V) ≃ V,
    (∀ a b, ord.symm a < ord.symm b → S a ≤ S b) ∧
    ∀ k,
      (Finset.univ.filter fun i =>
          ord.symm i < ord.symm k ∧ S i ≤ S k ∧ S k < S i + p i).card < m ∧
      AvailAtDecision A r p S ord k k ∧
      (IsFirstWith L (fun i => ord.symm k ≤ ord.symm i) k ∨
        ((∃ i, IsFirstWith L (fun i => ord.symm k ≤ ord.symm i) i ∧
            ¬ AvailAtDecision A r p S ord k i) ∧
          IsFirstWith L (fun i => ord.symm k ≤ ord.symm i ∧ AvailAtDecision A r p S ord k i) k ∧
          β * μ k ≤ charge m A r L p S k (S k)))) ∧
  (∀ t : ℝ, busy p S t < m →
    ∀ i, IsFirstWith L (fun i => t < S i) i → ¬ avail A r p S i t) ∧
  (∀ (t : ℝ) (k : V), busy p S t < m → IsDelayed A r L p S k t →
    charge m A r L p S k t < β * μ k)

/-- A CMNS policy: a map `σ` from realizations to start times such that `σ p` is the schedule
constructed by Algorithm CMNS for every nonnegative realization `p`. -/
def IsCMNSPolicy (m : ℕ) (A : V → V → Prop) (r : V → ℝ) (L : Fin (Fintype.card V) ≃ V)
    (β : ℝ) (μ : V → ℝ) (σ : (V → ℝ) → V → ℝ) : Prop :=
  ∀ p : V → ℝ, (∀ j, 0 ≤ p j) → IsCMNSRun m A r L β μ p (σ p)

/-- `O_j(p)`: the jobs of `A_j` (after `j` in `L`) that are started before `j` in the schedule `S`,
i.e. out of order with respect to `j`. -/
noncomputable def outOfOrder (L : Fin (Fintype.card V) ≃ V) (S : V → ℝ) (j : V) : Finset V :=
  (after L j).filter fun i => S i < S j

end StochSchedPrec.CMNS


