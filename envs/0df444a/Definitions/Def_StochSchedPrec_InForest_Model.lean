-- Prove2me | Definitions.Def_StochSchedPrec_InForest_Model
-- name    : StochSchedPrec_InForest_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T08:43:44.882298+00:00
-- url     : https://prove2.me/theorems/4c5be50a-46e6-4b0a-88f7-0b5f5afc4503
-- title:
--   §1 and §3, pp. 788–796 — stochastic instance without release dates, feasible schedules, nonanticipatory policies, the CV bound
-- statement:
--   This file fixes the stochastic scheduling model of Skutella and Uetz (§1, pp. 788–789), specialised to the case without release dates used in §4 for in-forest precedence constraints (p. 799).
--
--   **Jobs and precedence constraints.** A finite set $V$ of jobs is to be scheduled on $m$ identical parallel machines, nonpreemptively. Precedence constraints are given by a digraph $G=(V,A)$; an arc $(i,j)\in A$ means that $j$ may start only after $i$ has completed. The digraph is *acyclic* if no job is its own predecessor along a directed path. It is an *in-forest* if each job has at most one successor, that is, at most one outgoing arc.
--
--   **Schedules.** For a realization $p=(p_j)_{j\in V}$ of the processing times, with $p_j\ge 0$, a schedule is a vector of start times $S=(S_j)$, with completion times $C_j=S_j+p_j$. It is *feasible on $m$ machines* if
--   1. $S_j\ge 0$ for every job $j$ (there are no release dates);
--   2. $S_i+p_i\le S_j$ for every arc $(i,j)\in A$;
--   3. at every time $t$, at most $m$ jobs are in process, a job $k$ being in process at $t$ when $S_k\le t<S_k+p_k$.
--
--   **Policies.** A scheduling policy $\Pi$ is viewed as the map $p\mapsto S^\Pi(p)$ from realizations to start times. It is *feasible* if $S^\Pi(p)$ is a feasible schedule for every nonnegative $p$, and *nonanticipatory* if its decisions up to time $t$ depend only on what has been observed by $t$: whenever two nonnegative realizations $p,p'$ agree on the processing times of the jobs completed by $t$ under $\Pi$ for $p$, and every job in process at $t$ under $\Pi$ for $p$ is still in process at $t$ under $p'$, then $\Pi$ has started exactly the same jobs at the same times by $t$ under $p$ and under $p'$.
--
--   **Processing times.** The processing times are random variables $P_j$ on a probability space $(\Omega,\Pr)$: measurable, nonnegative, and stochastically independent. The *coefficient-of-variation bound* $\mathrm{CV}[P_j]\le\sqrt\Delta$ for all $j$ and some $\Delta\ge 0$ (§3, p. 796) is the condition
--   $$\operatorname{Var}[P_j]\le \Delta\, \mathrm E[P_j]^2\qquad (j\in V),$$
--   together with $\mathrm E[P_j^2]<\infty$ and $\mathrm E[P_j]>0$. A *comparator policy* is a feasible nonanticipatory policy whose completion times $C^\Pi_j(P)=S^\Pi_j(P)+P_j$ are integrable.
--
--   These objects are the common setting of every statement of the mission.
--
--   **Formalization Note** Machine capacity is encoded by counting the jobs in process (half-open intervals), which for identical machines is equivalent to the existence of a nonpreemptive machine assignment. The CV bound includes finiteness of the second moment, because Mathlib's `variance` is $0$ when the variance is infinite, and positivity of the mean, without which $\mathrm{CV}[P_j]=\sqrt{\operatorname{Var}[P_j]}/\mathrm E[P_j]$ is undefined. Integrability of the comparator's completion times loses nothing: a policy with $\mathrm E[C^\Pi_j]=\infty$ satisfies every upper bound of the mission trivially.
-- source:
--   Skutella and Uetz, Stochastic machine scheduling with precedence constraints, SIAM J. Comput. 34(4) (2005) 788–802, pp. 788–789 (§1, model and dynamic view of policies), p. 796 (§3, CV bound), p. 799 (§4, in-forest, no release dates)

import Mathlib

namespace StochSchedPrec.InForest

open MeasureTheory ProbabilityTheory

variable {V : Type*}

/-- The precedence digraph `A` (arcs `A i j`, "`i` must complete before `j` starts") is acyclic:
no job is its own (path) predecessor. -/
def IsAcyclic (A : V → V → Prop) : Prop :=
  ∀ j, ¬ Relation.TransGen A j j

/-- In-forest precedence constraints (§4, p. 799): each job has at most one successor, i.e.
at most one outgoing arc of `A`. -/
def IsInForest (A : V → V → Prop) : Prop :=
  ∀ i j k, A i j → A i k → j = k

/-- A realization of the processing times: every coordinate is nonnegative. -/
def IsNonneg (p : V → ℝ) : Prop :=
  ∀ j, 0 ≤ p j

/-- `S` (start times) is a feasible nonpreemptive schedule on `m` identical parallel machines
for the realization `p`, without release dates (§1, pp. 788–789, and §4, p. 799):
1. no job starts before time `0`;
2. for every arc `(i, j)`, job `j` starts no earlier than the completion time `S i + p i`;
3. at every time `t` at most `m` jobs are in process, a job `k` being in process at `t` when
   `S k ≤ t < S k + p k` (half-open intervals). -/
def IsFeasibleSchedule [Fintype V] (A : V → V → Prop) (m : ℕ) (p S : V → ℝ) : Prop :=
  (∀ j, 0 ≤ S j) ∧
  (∀ i j, A i j → S i + p i ≤ S j) ∧
  (∀ t : ℝ, (Finset.univ.filter fun j => S j ≤ t ∧ t < S j + p j).card ≤ m)

/-- A policy `pol` (the paper's `Π`), viewed as the map from realizations to start-time vectors, is
nonanticipatory: if two nonnegative realizations `p, p'` agree on everything observed by
time `t` under `pol p` (the processing time of every job completed by `t`, and the fact that
every job in process at `t` is still in process), then `pol p'` has started exactly the same
jobs at the same times by `t`. -/
def IsNonanticipatory (pol : (V → ℝ) → (V → ℝ)) : Prop :=
  ∀ (t : ℝ) (p p' : V → ℝ), IsNonneg p → IsNonneg p' →
    (∀ i, pol p i ≤ t →
      (pol p i + p i ≤ t → p' i = p i) ∧ (t < pol p i + p i → t < pol p i + p' i)) →
    ∀ i, (pol p i ≤ t ↔ pol p' i ≤ t) ∧ (pol p i ≤ t → pol p' i = pol p i)

/-- A (feasible, nonanticipatory) scheduling policy on `m` machines for the precedence
constraints `A` and no release dates: it yields a feasible schedule for every nonnegative
realization, and it is nonanticipatory. -/
def IsPolicy [Fintype V] (A : V → V → Prop) (m : ℕ) (pol : (V → ℝ) → (V → ℝ)) : Prop :=
  (∀ p, IsNonneg p → IsFeasibleSchedule A m p (pol p)) ∧ IsNonanticipatory pol

/-- The standing stochastic model (§1, p. 789): the processing times `P j` are measurable,
nonnegative random variables on the probability space `(Ω, Pr)`, and they are stochastically
independent. -/
def IsStochProcTimes {Ω : Type*} [MeasurableSpace Ω] (P : V → Ω → ℝ) (Pr : Measure Ω) : Prop :=
  (∀ j, Measurable (P j)) ∧ (∀ j ω, 0 ≤ P j ω) ∧ iIndepFun P Pr

/-- The coefficient-of-variation bound `CV[P_j] ≤ √Δ` for all jobs (§3, p. 796): `Δ ≥ 0`,
every `P j` has a finite second moment and a positive mean, and
`Var[P_j] ≤ Δ · E[P_j]^2`. -/
def CVBound {Ω : Type*} [MeasurableSpace Ω] (P : V → Ω → ℝ) (Pr : Measure Ω) (Δ : ℝ) : Prop :=
  0 ≤ Δ ∧ (∀ j, MemLp (P j) 2 Pr) ∧ (∀ j, 0 < ∫ ω, P j ω ∂Pr) ∧
    (∀ j, variance (P j) Pr ≤ Δ * (∫ ω, P j ω ∂Pr) ^ 2)

/-- A comparator policy: a feasible nonanticipatory policy whose completion times
`C^Π_j(P) = S^Π_j(P) + P_j` (with `Π = pol`) are integrable random variables. -/
def IsComparator [Fintype V] {Ω : Type*} [MeasurableSpace Ω] (A : V → V → Prop) (m : ℕ)
    (P : V → Ω → ℝ) (Pr : Measure Ω) (pol : (V → ℝ) → (V → ℝ)) : Prop :=
  IsPolicy A m pol ∧ ∀ j, Integrable (fun ω => pol (fun k => P k ω) j + P j ω) Pr

end StochSchedPrec.InForest


