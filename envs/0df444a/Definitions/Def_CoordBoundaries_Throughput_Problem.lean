-- Prove2me | Definitions.Def_CoordBoundaries_Throughput_Problem
-- name    : CoordBoundaries_Throughput_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:31:26.613191+00:00
-- url     : https://prove2.me/theorems/45729214-b19d-4fd3-9fa5-65ebd6a3f242
-- title:
--   Throughput maximization on identical machines: instances, feasible schedules, OPT, encoding and expected approximation
-- statement:
--   An **instance** consists of $m$ identical machines and $n$ jobs; job $j$ has a processing time $p_j>0$, a release time $r_j\ge 0$ and a deadline $d_j>r_j$, all integers. Its **window** is $[r_j,d_j)$ and the **time horizon** is $T=\max_j d_j$ ($T=0$ for $n=0$).
--
--   A **schedule** selects some jobs and gives each selected job a machine $i$ and a real start time $S_j$. It is **feasible** when every selected job runs once, continuously, inside its window ($r_j\le S_j$ and $S_j+p_j\le d_j$), and two jobs on the same machine never overlap. The **throughput** is the number of selected jobs, and
--   $$\mathrm{OPT}=\max\{|A| : A \text{ is the job set of a feasible schedule}\},$$
--   a maximum over a finite nonempty family (the empty schedule is feasible).
--
--   Algorithms are programs of the published integer RAM `CongruencyTU_Machine` (unit-cost $+,-,\times$, integer division and remainder, comparisons, indirect addressing, and a coin instruction). The input is the binary encoding $[m,n,p_0,r_0,d_0,\dots]$ of the instance; its bit size is the **input length** $N$. An output is a list of triples $(j,i,S)$ (job, machine, integer start time) without repeated jobs; anything else is not a schedule.
--
--   A program is an **expected $\rho$-approximation within budget $B(I)$** on a class of instances if on every valid instance of the class, for every string of $B(I)$ random bits, the run halts within cost $B(I)$, keeps every register within $q(N)$ bits for a polynomial $q$ fixed in advance, and outputs a feasible schedule; and the throughput averaged uniformly over the $2^{B(I)}$ bit strings is at least $\mathrm{OPT}/\rho$. The variant **retaining fraction $\phi(I)$** asks for expected throughput at least $\phi(I)\cdot\mathrm{OPT}$.
--
--   These are the objects of Theorem 1.1: every algorithmic statement of the mission is a statement about these predicates.
--
--   **Formalization Note** Time data are natural numbers. The expected throughput is written as the requirement $\mathrm{OPT}\le\rho\cdot\mathbb E[\text{throughput}]$. An output that does not decode counts as infeasible (and as throughput $0$).
-- source:
--   Tong and Xu, Coordinating Boundaries: Improved Approximation Algorithms for Unweighted Non-Preemptive Throughput Maximization, preprint of October 25, 2026 (STOC 2027 submission #141; source.pdf sha256 59f76539a5ee555f9e56603a067e9f858f38d003011e90b1716085348673687e), p. 2, §1 (problem, OPT, expected ρ-approximation); p. 8 (integer start times); pp. 26–27, §4.5 (draws implemented with unbiased bits)

import Mathlib
import Definitions.Def_CongruencyTU_Machine

open Classical

namespace CoordBoundaries.Throughput

open CongruencyTU

/-! # Unweighted nonpreemptive throughput maximization (Tong–Xu, §1, p. 2)

An instance has `m` identical machines and `n` jobs; job `j` has processing time `p j`, release
time `r j` and deadline `d j`, all natural numbers (the source's "integers, `r_j ≥ 0`"). A schedule
assigns each selected job a machine and a real start time `S` with `r j ≤ S`, `S + p j ≤ d j`, and
no two jobs overlap on one machine. `OPT` is the maximum number of scheduled jobs. Algorithms are
programs of the published integer RAM `CongruencyTU` (unit-cost arithmetic, coins, registers of
polynomially many bits); the input is the binary encoding `enc I`, of bit size `N I`. -/

/-- An instance: `m` machines, `n` jobs with processing times `p`, release times `r`, deadlines `d`. -/
structure Instance where
  m : ℕ
  n : ℕ
  p : Fin n → ℕ
  r : Fin n → ℕ
  d : Fin n → ℕ

namespace Instance

/-- The source's standing data conditions (p. 2): `p_j > 0` and `d_j > r_j`. -/
def Valid (I : Instance) : Prop := ∀ j, 0 < I.p j ∧ I.r j < I.d j

/-- The time horizon `T = max_j d_j` (`0` for the empty instance). -/
def T (I : Instance) : ℕ := Finset.univ.sup I.d

end Instance

/-- A schedule: each job is either unscheduled (`none`) or executed on a machine from a real
start time. -/
abbrev Sched (I : Instance) := Fin I.n → Option (Fin I.m × ℝ)

/-- Feasibility (p. 2): each selected job runs once, continuously for `p j` time units inside its
window `[r j, d j)`, with no overlap on the same machine. -/
def Feasible (I : Instance) (σ : Sched I) : Prop :=
  (∀ (j : Fin I.n) (i : Fin I.m) (S : ℝ), σ j = some (i, S) →
      (I.r j : ℝ) ≤ S ∧ S + I.p j ≤ I.d j) ∧
  (∀ (j k : Fin I.n) (i : Fin I.m) (S S' : ℝ), j ≠ k → σ j = some (i, S) → σ k = some (i, S') →
      S + I.p j ≤ S' ∨ S' + I.p k ≤ S)

/-- The set of jobs a schedule executes. -/
noncomputable def scheduled {I : Instance} (σ : Sched I) : Finset (Fin I.n) :=
  Finset.univ.filter fun j => (σ j).isSome

/-- `OPT`: the maximum throughput over feasible schedules with real start times. It is a maximum
over a finite nonempty family (the empty schedule is feasible). -/
noncomputable def OPT (I : Instance) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin I.n))).filter
    fun A => ∃ σ : Sched I, Feasible I σ ∧ scheduled σ = A).sup Finset.card

/-- Binary input encoding: `[m, n, p 0, r 0, d 0, …]`. -/
def enc (I : Instance) : List ℤ :=
  [(I.m : ℤ), (I.n : ℤ)] ++
    (List.finRange I.n).flatMap fun j => [(I.p j : ℤ), (I.r j : ℤ), (I.d j : ℤ)]

/-- The input length `N`: the bit size of `enc I`. -/
def N (I : Instance) : ℕ := bitSize (enc I)

/-- Split a flat list into triples (fails if the length is not a multiple of three). -/
def triples : List ℤ → Option (List (ℤ × ℤ × ℤ))
  | a :: b :: c :: rest => (triples rest).map ((a, b, c) :: ·)
  | [] => some []
  | _ => none

/-- Output decoding: a flat list of triples `(j, i, S)` (job, machine, integer start time) with
`0 ≤ j < n`, `0 ≤ i < m` and no repeated job. Anything else decodes to `none`. -/
noncomputable def decode (I : Instance) (out : List ℤ) : Option (Sched I) :=
  match triples out with
  | none => none
  | some ts =>
    if (∀ t ∈ ts, 0 ≤ t.1 ∧ t.1 < (I.n : ℤ) ∧ 0 ≤ t.2.1 ∧ t.2.1 < (I.m : ℤ)) ∧
        (ts.map Prod.fst).Nodup then
      some fun j =>
        match ts.find? (fun t => t.1 == (j : ℤ)) with
        | none => none
        | some t =>
          if h : t.2.1.toNat < I.m then some (⟨t.2.1.toNat, h⟩, (t.2.2 : ℝ)) else none
    else none

/-- The output decodes to a feasible schedule. -/
def OutFeasible (I : Instance) (out : List ℤ) : Prop :=
  ∃ σ, decode I out = some σ ∧ Feasible I σ

/-- Throughput of an output (`0` if it does not decode). -/
noncomputable def thr (I : Instance) (out : List ℤ) : ℕ :=
  match decode I out with
  | some σ => (scheduled σ).card
  | none => 0

/-- Expected throughput of program `P` on `I` with `B` uniformly random coins. -/
noncomputable def expThr (P : Program) (I : Instance) (B : ℕ) : ℝ :=
  (∑ c : Fin B → Bool, (thr I (outputAfter P noOracle (extendCoins c) (enc I) B) : ℝ)) / 2 ^ B

/-- On every coin string the run halts within cost `B` with registers of at most `q(N)` bits, and
its output is a feasible schedule. -/
def AlwaysFeasibleWithin (P : Program) (q : Polynomial ℕ) (I : Instance) (B : ℕ) : Prop :=
  (∀ c : Fin B → Bool, RunBounded P noOracle (extendCoins c) (enc I) B q 0) ∧
  (∀ c : Fin B → Bool, OutFeasible I (outputAfter P noOracle (extendCoins c) (enc I) B))

/-- **Expected `ρ`-approximation within a budget** (p. 2): one program and one bit-length polynomial,
fixed before the input, such that on every valid instance in `Dom` every coin string gives a run of
cost at most `budget I` with a feasible output, and the expected throughput is at least `OPT/ρ`
(written `OPT ≤ ρ · E`). -/
def ApproxWithin (ρ : ℝ) (Dom : Instance → Prop) (budget : Instance → ℕ) : Prop :=
  ∃ (P : Program) (q : Polynomial ℕ), ∀ I : Instance, I.Valid → Dom I →
    AlwaysFeasibleWithin P q I (budget I) ∧ (OPT I : ℝ) ≤ ρ * expThr P I (budget I)

/-- **Retained fraction within a budget**: as `ApproxWithin`, with the guarantee
`E[throughput] ≥ frac I · OPT`. -/
def RetainsWithin (frac : Instance → ℝ) (Dom : Instance → Prop) (budget : Instance → ℕ) : Prop :=
  ∃ (P : Program) (q : Polynomial ℕ), ∀ I : Instance, I.Valid → Dom I →
    AlwaysFeasibleWithin P q I (budget I) ∧ frac I * (OPT I : ℝ) ≤ expThr P I (budget I)

/-- A deterministic output solves `I` exactly: it is a feasible schedule of cardinality `OPT`. -/
def SolvesExactly (I : Instance) (out : List ℤ) : Prop :=
  OutFeasible I out ∧ thr I out = OPT I

end CoordBoundaries.Throughput


