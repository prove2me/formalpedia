-- Prove2me | Definitions.Def_FixedMachinePrec_Instance
-- name    : FixedMachinePrec_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:09.677608+00:00
-- url     : https://prove2.me/theorems/056cd36d-d7a9-44d0-b105-66a77b728033
-- title:
--   Instances of $Pm\mid prec, p_j=1\mid C_{\max}$, real-time schedules, makespan, optimum and deadline feasibility
-- statement:
--   An **instance** consists of $n$ unit-time jobs, identified with the vertices of a directed graph $G=(V,E)$, $V=\{1,\dots,n\}$, given by its list of arcs. Write $x\prec y$ when $G$ has a directed path of positive length from $x$ to $y$; $G$ is **acyclic** when no job precedes itself.
--
--   A **schedule** on $m$ identical machines assigns to every job $x$ a real start time $S_x$ and a machine $\mu(x)\in\{1,\dots,m\}$; job $x$ runs during $[S_x,S_x+1)$. It is **feasible** if
--
--   1. $S_x\ge 0$ for every job,
--   2. two distinct jobs on the same machine do not overlap: $S_x+1\le S_y$ or $S_y+1\le S_x$,
--   3. $x\prec y$ implies $S_x+1\le S_y$.
--
--   The **makespan** is $C_{\max}=\max_x (S_x+1)$, and $0$ when $n=0$. A schedule is **optimum** if it is feasible and its makespan is at most that of every feasible schedule; the instance is **feasible by the deadline** $T$ if some feasible schedule has $C_{\max}\le T$.
--
--   An **integral schedule** assigns each job a slot $\tau(x)$ (slot $t$ means execution during $[t-1,t)$) and a machine number; it *realizes* the real-time schedule with $S_x=\tau(x)-1$ and the same machines. A **slot schedule of deadline** $T$ assigns slots in $\{1,\dots,T\}$ with at most $m$ jobs per slot and $\tau(x)<\tau(y)$ whenever $x\prec y$.
--
--   These are the objects of the problem $Pm\mid prec, p_j=1\mid C_{\max}$; optimality is always measured against all schedules with real start times.
--
--   **Formalization Note** Jobs are `Fin n` and machines `Fin m` (0-based); machine numbers of integral schedules are 0-based naturals, slots are 1-based. Acyclicity and distinctness of arcs are hypotheses of the theorems.
-- source:
--   K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines, manuscript dated 1 November 2026 (sha256 08cdf3e1…), §1, p.1; §2.1, p.4 (slot schedules)

import Mathlib

namespace FixedMachinePrec

/-- **An instance of `Pm | prec, p_j = 1 | Cmax`: a precedence digraph on `n` unit jobs.**
Jansen, *Precedence Constraint Scheduling on a Fixed Number of Machines* (manuscript, sha256
08cdf3e1…), §1, p.1: "We are given a directed acyclic graph G = (V, E) and m identical machines.
Each vertex is a job of processing time one. … Vertices 1, . . . , n are individually listed,
including isolated vertices; arcs are distinct and use standard binary vertex labels."

**Formalization Note** Jobs are `Fin n` (0-based: the paper's vertex `j` is `j - 1`). The arcs are
a `List` in the order in which the input lists them; distinctness (`arcs.Nodup`) and acyclicity
(`Acyclic`) are hypotheses of the theorems, not fields. The number of machines `m` is a separate
argument everywhere. -/
structure Instance where
  /-- the number of jobs `n = |V|` -/
  n : ℕ
  /-- the arcs of `G`, in input order -/
  arcs : List (Fin n × Fin n)

namespace Instance

variable (G : Instance)

/-- `(x, y)` is an arc of `G`. -/
def Arc (x y : Fin G.n) : Prop := (x, y) ∈ G.arcs

/-- `x ≺ y`: there is a directed path of positive length from `x` to `y` in `G` (Jansen, §2.1,
p.4: "Write x ≺ y when there is a directed path of positive length from x to y"). -/
def Prec (x y : Fin G.n) : Prop := Relation.TransGen G.Arc x y

/-- `G` is acyclic: no job precedes itself. -/
def Acyclic : Prop := ∀ x, ¬ G.Prec x x

end Instance

/-- **A nonpreemptive schedule with real start times** on `m` identical machines: job `x` runs on
machine `machine x` during `[start x, start x + 1)`.

**Formalization Note** Machines are `Fin m` (0-based: machine `0` is the paper's machine 1). -/
structure Schedule (G : Instance) (m : ℕ) where
  /-- the start time of each job -/
  start : Fin G.n → ℝ
  /-- the machine of each job -/
  machine : Fin G.n → Fin m

namespace Schedule

variable {G : Instance} {m : ℕ} (σ : Schedule G m)

/-- **Feasibility** (Jansen, §1, p.1: "A job can start only after all its predecessors have
finished. Jobs cannot be interrupted."): start times are nonnegative, two distinct jobs on one
machine do not overlap, and `x ≺ y` forces `start x + 1 ≤ start y`. -/
def Feasible : Prop :=
  (∀ x, 0 ≤ σ.start x) ∧
  (∀ x y, x ≠ y → σ.machine x = σ.machine y →
      σ.start x + 1 ≤ σ.start y ∨ σ.start y + 1 ≤ σ.start x) ∧
  (∀ x y, G.Prec x y → σ.start x + 1 ≤ σ.start y)

/-- **The makespan `Cmax`**, the time at which the last job finishes: `max_x (start x + 1)`, and
`0` when there are no jobs. -/
noncomputable def cmax : ℝ :=
  if h : 0 < G.n then Finset.univ.sup' ⟨⟨0, h⟩, Finset.mem_univ _⟩ (fun x => σ.start x + 1) else 0

end Schedule

/-- **An optimum schedule**: feasible, with makespan at most that of every feasible schedule with
real start times (Jansen, §1, p.1: "The objective is to minimize the time at which the last job
finishes"). -/
def IsOptimum {G : Instance} {m : ℕ} (σ : Schedule G m) : Prop :=
  σ.Feasible ∧ ∀ σ' : Schedule G m, σ'.Feasible → σ.cmax ≤ σ'.cmax

/-- **Deadline feasibility**: some feasible schedule has makespan at most `T` (Jansen, §1, p.1:
"decide deadline feasibility"; §3.2, p.10: "whether the jobs represented by G admit a feasible
schedule with makespan at most T"). -/
def DeadlineFeasible (G : Instance) (m T : ℕ) : Prop :=
  ∃ σ : Schedule G m, σ.Feasible ∧ σ.cmax ≤ T

/-- **An integral schedule** as the algorithms output it: job `x` gets slot `slot x` (slot `t`
means execution during `[t − 1, t)`, Jansen §2.1, p.4) and machine number `machine x`.

**Formalization Note** Slots are 1-based as printed; machine numbers are 0-based natural numbers
(`0` is the paper's machine 1). Validity (slots `≥ 1`, machine numbers `< m`) is not part of the
structure: it is imposed through `Realizes`. -/
structure SlotSchedule (G : Instance) where
  /-- the slot of each job, `≥ 1` in a valid schedule -/
  slot : Fin G.n → ℕ
  /-- the machine number of each job (0-based) -/
  machine : Fin G.n → ℕ

/-- `σ` is the integral schedule `ρ` read in real time: `start x = slot x − 1` and the same machine
numbers. -/
def SlotSchedule.Realizes {G : Instance} {m : ℕ} (σ : SlotSchedule G) (ρ : Schedule G m) : Prop :=
  ∀ x, ρ.start x = (σ.slot x : ℝ) - 1 ∧ (ρ.machine x : ℕ) = σ.machine x

/-- **An integral optimum schedule**: its real-time reading is an optimum schedule. -/
def SlotSchedule.IsOptimum {G : Instance} (m : ℕ) (σ : SlotSchedule G) : Prop :=
  ∃ ρ : Schedule G m, σ.Realizes ρ ∧ FixedMachinePrec.IsOptimum ρ

/-- **An integral schedule meeting the deadline `T`**: its real-time reading is feasible with
makespan at most `T`. -/
def SlotSchedule.MeetsDeadline {G : Instance} (m T : ℕ) (σ : SlotSchedule G) : Prop :=
  ∃ ρ : Schedule G m, σ.Realizes ρ ∧ ρ.Feasible ∧ ρ.cmax ≤ T

/-- **A slot schedule of deadline `T`** (Jansen, §2.1, p.4): "assigns each job a slot
τ(x) ∈ {1, . . . , T}, with at most m jobs per slot and τ(x) < τ(y) whenever x ≺ y". -/
def IsSlotSchedule (G : Instance) (m T : ℕ) (τ : Fin G.n → ℕ) : Prop :=
  (∀ x, 1 ≤ τ x ∧ τ x ≤ T) ∧
  (∀ t : ℕ, (Finset.univ.filter fun x => τ x = t).card ≤ m) ∧
  (∀ x y, G.Prec x y → τ x < τ y)

end FixedMachinePrec


