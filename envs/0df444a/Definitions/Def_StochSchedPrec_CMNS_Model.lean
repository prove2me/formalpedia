-- Prove2me | Definitions.Def_StochSchedPrec_CMNS_Model
-- name    : StochSchedPrec_CMNS_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:52:26.997903+00:00
-- url     : https://prove2.me/theorems/c2264bc2-f253-4724-bebf-aca3129c2810
-- title:
--   §1–§3, pp. 788–797 — stochastic instances, feasible schedules, nonanticipatory policies, f(W), the LP relaxation and critical chains
-- statement:
--   This file fixes the model of Skutella and Uetz for stochastic scheduling on parallel identical machines with precedence constraints and release dates, $\mathrm P\,|\,r_j,\mathit{prec}\,|\,\mathrm E[\sum w_jC_j]$.
--
--   **Instance.** A finite set $V$ of jobs is to be scheduled nonpreemptively on $m\ge 1$ identical machines. Precedence constraints are the arcs $A$ of an acyclic digraph on $V$; job $i$ is a *predecessor* of $j$ if there is a directed path from $i$ to $j$. Job $j$ has a release date $r_j\ge 0$ and a weight $w_j\ge 0$. The processing times are random variables $P_1,\dots,P_n$ on a probability space: they are nonnegative, measurable, have finite expectation $\mathrm E[P_j]$, and are stochastically independent. A realization is a vector $p=(p_j)_{j\in V}$ with $p_j\ge 0$.
--
--   **Schedules.** For a realization $p$, a vector of start times $S$ is a *feasible schedule on $m$ machines* if $S_j\ge r_j$ for every job, $S_i+p_i\le S_j$ for every arc $(i,j)\in A$, and at every time $t$ at most $m$ jobs are in process, job $j$ being in process during $[S_j,S_j+p_j[$. The completion time is $C_j=S_j+p_j$.
--
--   **Policies.** A scheduling policy $\Pi$ maps every nonnegative realization $p$ to a feasible schedule $S^\Pi(p)$. It is *nonanticipatory* if, whenever a second realization $p'$ agrees with everything observed by time $t$ under $p$ (the processing times of the jobs completed by $t$, and the fact that the jobs in process at $t$ are not yet completed), $\Pi$ has started the same jobs at the same times by $t$ under $p'$ as under $p$. An *admissible comparator policy* is a feasible nonanticipatory policy whose completion times $C^\Pi_j(P)=S^\Pi_j(P)+P_j$ are integrable.
--
--   **The CV bound.** For $\Delta\ge0$, the coefficients of variation are bounded by $\sqrt\Delta$: every $P_j$ has a finite second moment, $\mathrm E[P_j]>0$, and $\mathrm{Var}[P_j]\le\Delta\,\mathrm E[P_j]^2$.
--
--   **The LP relaxation.** With $\mu_j=\mathrm E[P_j]$, the set function (3.1) is
--   $$f(W)=\frac1{2m}\Big(\big(\textstyle\sum_{j\in W}\mu_j\big)^2+\sum_{j\in W}\mu_j^2\Big)-\frac{(m-1)(\Delta-1)}{2m}\sum_{j\in W}\mu_j^2,\qquad W\subseteq V.$$
--   A vector $C^{\mathrm{LP}}$ is LP-feasible if $\sum_{j\in W}\mu_jC^{\mathrm{LP}}_j\ge f(W)$ for all $W\subseteq V$, $C^{\mathrm{LP}}_j\ge C^{\mathrm{LP}}_i+\mu_j$ for $(i,j)\in A$, and $C^{\mathrm{LP}}_j\ge\mu_j$; it is LP-optimal if it minimizes $\sum_jw_jC^{\mathrm{LP}}_j$ among LP-feasible points.
--
--   **Lists.** A priority list $L$ is a numbering of the jobs. $B_j$ is the set of jobs that come before $j$ in $L$, including $j$, and $A_j$ the set of jobs after $j$. $L$ is a *linear extension* if every predecessor of a job comes earlier in $L$; it is *ordered by* $C$ if $C$ is nondecreasing along $L$.
--
--   **Availability and critical chains** (p. 792). Job $j$ is *available* at time $t$ if $r_j\le t$ and all its predecessors are completed by $t$; $r_j(p)=\max\{r_j,\max_{i\text{ pred. of }j}C_i\}$ is the earliest such time. A *critical predecessor* of $j$ (Definition 2.2) is a predecessor $i$ with $C_i>r_j$ and $C_i$ maximal among all predecessors; ties are broken by a fixed tie-breaking order. The length $\ell_j(p)$ of the critical chain (Definition 2.3) is defined backwards: $\ell_j(p)=r_j+p_j$ if $j$ has no critical predecessor, and $\ell_j(p)=p_j+\ell_k(p)$ for the critical predecessor $k$ otherwise.
--
--   These objects are shared by every statement of the mission: the algorithm, its analysis, and the comparator side.
--
--   **Formalization Note** Jobs form a `Fintype`; arcs are a relation `A`, predecessors its transitive closure. Machine capacity is stated in counting form (at most $m$ jobs in process at any time, with half-open intervals); for identical machines this is equivalent to the existence of a nonpreemptive machine assignment. Zero processing times are allowed; a job of length zero is in process at no instant. The CV bound includes `MemLp 2` (otherwise Mathlib's `variance` of a non-square-integrable variable is $0$) and $\mathrm E[P_j]>0$ (CV is undefined otherwise). Expectations are Bochner integrals; finiteness of $\mathrm E[P_j]$ is part of the standing model. The critical-chain length is computed by a recursion with a step budget $|V|$, never exhausted on acyclic precedence constraints; the tie-breaking order `tb` is a parameter of every statement that uses $\ell_j$.
-- source:
--   Skutella and Uetz, Stochastic machine scheduling with precedence constraints, SIAM J. Comput. 34(4) (2005) 788–802, pp. 788–789 (§1, model and policies), p. 792 (availability, Assumption 2.1, Definitions 2.2, 2.3), pp. 796–797 ((3.1), CV, LP relaxation)

import Mathlib

namespace StochSchedPrec.CMNS

open MeasureTheory ProbabilityTheory

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of jobs in process at time `t` when job `j` occupies the half-open interval
`[S j, S j + p j)`. A job of length zero is in process at no instant. -/
noncomputable def busy (p S : V → ℝ) (t : ℝ) : ℕ :=
  (Finset.univ.filter fun j => S j ≤ t ∧ t < S j + p j).card

/-- `S` (start times) is a feasible nonpreemptive schedule on `m` identical parallel machines
for the realization `p` of the processing times, the arcs `A` and the release dates `r`:
no job starts before its release date, a job starts only after each of its arc predecessors
has completed, and at every time at most `m` jobs are in process. -/
def IsFeasible (m : ℕ) (A : V → V → Prop) (r p S : V → ℝ) : Prop :=
  (∀ j, r j ≤ S j) ∧ (∀ i j, A i j → S i + p i ≤ S j) ∧ ∀ t : ℝ, busy p S t ≤ m

/-- A (feasible) scheduling policy: a map `Π` from realizations of the processing times to start
times that yields a feasible `m`-machine schedule for every nonnegative realization. -/
def IsPolicy (m : ℕ) (A : V → V → Prop) (r : V → ℝ) (pol : (V → ℝ) → V → ℝ) : Prop :=
  ∀ p : V → ℝ, (∀ j, 0 ≤ p j) → IsFeasible m A r p (pol p)

/-- Nonanticipation (§1, p. 789): if a second realization `p'` agrees with everything observed by
time `t` under `p` (the processing times of the jobs completed by `t`, and the fact that the jobs
in process at `t` have not completed), then `Π p'` has started exactly the same jobs at the same
times by `t`. -/
def IsNonanticipatory (pol : (V → ℝ) → V → ℝ) : Prop :=
  ∀ (t : ℝ) (p p' : V → ℝ), (∀ j, 0 ≤ p j) → (∀ j, 0 ≤ p' j) →
    (∀ i, pol p i ≤ t →
      (pol p i + p i ≤ t → p' i = p i) ∧ (t < pol p i + p i → t < pol p i + p' i)) →
    ∀ i, (pol p i ≤ t ↔ pol p' i ≤ t) ∧ (pol p i ≤ t → pol p' i = pol p i)

/-- The standing stochastic model (§1, p. 789): the processing times `P j` are measurable,
nonnegative random variables with finite expectation, and they are stochastically
independent. -/
def IsStochModel {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) (P : V → Ω → ℝ) : Prop :=
  (∀ j, Measurable (P j)) ∧ (∀ j ω, 0 ≤ P j ω) ∧ (∀ j, Integrable (P j) Pr) ∧ iIndepFun P Pr

/-- The coefficient-of-variation bound `CV[P_j] ≤ √Δ` for all jobs (§3, p. 796): each `P j` has a
finite second moment and a positive mean, and `Var[P_j] ≤ Δ · E[P_j]^2`. -/
def HasCVBound {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) (P : V → Ω → ℝ) (Δ : ℝ) : Prop :=
  ∀ j, MemLp (P j) 2 Pr ∧ 0 < ∫ ω, P j ω ∂Pr ∧ variance (P j) Pr ≤ Δ * (∫ ω, P j ω ∂Pr) ^ 2

/-- An admissible comparator policy: a feasible, nonanticipatory policy whose completion times
`C^Π_j(P) = S^Π_j(P) + P_j` are integrable. -/
def IsAdmissiblePolicy (m : ℕ) (A : V → V → Prop) (r : V → ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (Pr : Measure Ω) (P : V → Ω → ℝ) (pol : (V → ℝ) → V → ℝ) : Prop :=
  IsPolicy m A r pol ∧ IsNonanticipatory pol ∧
    ∀ j, Integrable (fun ω => pol (fun k => P k ω) j + P j ω) Pr

/-- The set function `f` of (3.1), p. 796, with `μ j = E[P_j]`:
`f(W) = (1/(2m)) ((∑_{j∈W} μ_j)^2 + ∑_{j∈W} μ_j^2) - ((m-1)(Δ-1)/(2m)) ∑_{j∈W} μ_j^2`. -/
noncomputable def loadFn (m : ℕ) (Δ : ℝ) (μ : V → ℝ) (W : Finset V) : ℝ :=
  1 / (2 * (m : ℝ)) * ((∑ j ∈ W, μ j) ^ 2 + ∑ j ∈ W, μ j ^ 2)
    - ((m : ℝ) - 1) * (Δ - 1) / (2 * (m : ℝ)) * ∑ j ∈ W, μ j ^ 2

/-- A feasible point of the LP relaxation (§3, p. 797): the load inequalities for every
`W ⊆ V`, the arc inequalities `C_j ≥ C_i + μ_j` for `(i, j) ∈ A`, and `C_j ≥ μ_j`. -/
def IsLPFeasible (m : ℕ) (A : V → V → Prop) (Δ : ℝ) (μ : V → ℝ) (C : V → ℝ) : Prop :=
  (∀ W : Finset V, loadFn m Δ μ W ≤ ∑ j ∈ W, μ j * C j) ∧
    (∀ i j, A i j → C i + μ j ≤ C j) ∧ ∀ j, μ j ≤ C j

/-- An optimal solution of the LP relaxation: LP-feasible and minimizing `∑_j w_j C_j` among all
LP-feasible points. -/
def IsLPOptimal (m : ℕ) (A : V → V → Prop) (Δ : ℝ) (μ w : V → ℝ) (C : V → ℝ) : Prop :=
  IsLPFeasible m A Δ μ C ∧
    ∀ C' : V → ℝ, IsLPFeasible m A Δ μ C' → ∑ j, w j * C j ≤ ∑ j, w j * C' j

/-- A priority list `L` (`L k` is the job in position `k`) is ordered by nondecreasing `C`. -/
def IsSortedBy (L : Fin (Fintype.card V) ≃ V) (C : V → ℝ) : Prop :=
  ∀ k l : Fin (Fintype.card V), k ≤ l → C (L k) ≤ C (L l)

/-- The list `L` is a linear extension of the precedence constraints: every predecessor of a job
comes earlier in the list. -/
def IsLinearExtension (A : V → V → Prop) (L : Fin (Fintype.card V) ≃ V) : Prop :=
  ∀ i j, Relation.TransGen A i j → L.symm i < L.symm j

/-- `B_j`: the jobs that come before `j` in the list `L`, including `j` itself. -/
def before (L : Fin (Fintype.card V) ≃ V) (j : V) : Finset V :=
  Finset.univ.filter fun i => L.symm i ≤ L.symm j

/-- `A_j`: the jobs that come after `j` in the list `L`. -/
def after (L : Fin (Fintype.card V) ≃ V) (j : V) : Finset V :=
  Finset.univ.filter fun i => L.symm j < L.symm i

/-- Job `j` is available at time `t` in the schedule `S` (p. 792): it is released (`r_j ≤ t`) and
every predecessor of `j` has completed by `t`. -/
def avail (A : V → V → Prop) (r p S : V → ℝ) (j : V) (t : ℝ) : Prop :=
  r j ≤ t ∧ ∀ i, Relation.TransGen A i j → S i + p i ≤ t

open Classical in
/-- `r_j(p)`: the earliest time at which job `j` is available in the schedule `S`,
`max(r_j, max_{i predecessor of j} C_i)`. -/
noncomputable def availTime (A : V → V → Prop) (r p S : V → ℝ) (j : V) : ℝ :=
  Finset.fold max (r j) (fun i => S i + p i)
    (Finset.univ.filter fun i => Relation.TransGen A i j)

open Classical in
/-- The critical predecessor of `j` (Definition 2.2, p. 792) chosen by the fixed tie-breaking rule
`tb`: among the predecessors `i` of `j` with `C_i > r_j` and `C_i` maximal among all predecessors,
the one with the smallest `tb`-index; `none` if `j` has no critical predecessor. -/
noncomputable def critPred (A : V → V → Prop) (r : V → ℝ) (tb : V ≃ Fin (Fintype.card V))
    (p S : V → ℝ) (j : V) : Option V :=
  let M := Finset.univ.filter fun i => Relation.TransGen A i j ∧ r j < S i + p i ∧
    ∀ i', Relation.TransGen A i' j → S i' + p i' ≤ S i + p i
  if h : M.Nonempty then some (tb.symm ((M.image tb).min' (h.image tb))) else none

/-- Backwards recursion of Definition 2.3 with an explicit step budget. -/
noncomputable def chainLengthAux (A : V → V → Prop) (r : V → ℝ) (tb : V ≃ Fin (Fintype.card V))
    (p S : V → ℝ) : ℕ → V → ℝ
  | 0, j => r j + p j
  | n + 1, j =>
    match critPred A r tb p S j with
    | none => r j + p j
    | some i => p j + chainLengthAux A r tb p S n i

/-- The length `ℓ_j(p)` of the critical chain of `j` (Definition 2.3, p. 792): `r_j + p_j` if `j`
has no critical predecessor, and `p_j + ℓ_k(p)` for the critical predecessor `k` otherwise.
A critical chain has at most `|V|` jobs when the precedence digraph is acyclic, so the budget
`|V|` is never exhausted. -/
noncomputable def chainLength (A : V → V → Prop) (r : V → ℝ) (tb : V ≃ Fin (Fintype.card V))
    (p S : V → ℝ) (j : V) : ℝ :=
  chainLengthAux A r tb p S (Fintype.card V) j

end StochSchedPrec.CMNS


