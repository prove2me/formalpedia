-- Prove2me | Definitions.Def_AlgMechDesign_NonOptimal_Model
-- name    : AlgMechDesign_NonOptimal_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T21:36:57.093095+00:00
-- url     : https://prove2.me/theorems/122592f5-35e5-4add-97c7-c6841c061761
-- title:
--   Task scheduling with verification: the Compensation-and-Bonus mechanism based on an allocation algorithm, dominance and truthfulness
-- statement:
--   This file sets up **task scheduling with verification** (Nisan and Ronen, Definitions 18–20) and the **Compensation-and-Bonus mechanism based on an allocation algorithm** (Definitions 21–24 and 32).
--
--   There are $n \ge 1$ agents $i$ and $k$ tasks $j$. A **type vector** $t = (t^1,\dots,t^n)$ has positive entries $t^i_j$, the minimum time in which agent $i$ can perform task $j$. An **allocation** $x = (x^1,\dots,x^n)$ gives every task to exactly one agent ($x^i$ is the set of tasks of agent $i$; parts may be empty). The **make-span** of $x$ under $t$ is
--
--   $$g(x,t) = \max_{1\le i\le n} \sum_{j\in x^i} t^i_j ,$$
--
--   and $x$ is **optimal** for $t$ if $g(x,t) \le g(y,t)$ for every allocation $y$. For a vector $\tilde t = (\tilde t_1,\dots,\tilde t_k)$ of actual execution times, $g(x,\tilde t) = \max_i \sum_{j\in x^i}\tilde t_j$.
--
--   **Strategies.** An agent's strategy consists of a **declaration** $d^i$ (a positive vector, possibly different from its type) and an **execution plan** $e^i$, which says, for every allocation $x$ the mechanism may choose, in what time $\tilde t_j$ the agent performs each task $j \in x^i$. The plan is **feasible** for an agent of type $t^i$ if $\tilde t_j \ge t^i_j$ for every task it receives. The mechanism chooses $x = x(d)$ from the declarations alone, by a fixed **allocation algorithm** $d \mapsto x(d)$; each task is then performed by its agent in the time its plan prescribes, giving the vector $\tilde t$ of actual times.
--
--   **Payments.** The **compensation** of agent $i$ is $c^i(d,\tilde t) = \sum_{j\in x^i(d)} \tilde t_j$. The **corrected time vector** for agent $i$ is
--   $$\operatorname{corr}^i(x,d,\tilde t)_j = \begin{cases} \tilde t_j & j \in x^i,\\ d^l_j & j\in x^l,\ l\ne i,\end{cases}$$
--   and $\operatorname{corr}^*(x,d)_j = d^l_j$ for $j \in x^l$. The **bonus** is $b^i(d,\tilde t) = -g\bigl(x(d), \operatorname{corr}^i(x(d),d,\tilde t)\bigr)$. The Compensation-and-Bonus mechanism based on the algorithm $x(\cdot)$ pays $p^i = c^i + b^i$, and agent $i$'s utility is $p^i - \sum_{j\in x^i(d)} \tilde t_j$ (payment plus valuation).
--
--   **Dominance and truthfulness.** A strategy $(d^i, e^i)$ is **dominant** for agent $i$ of type $t^i$ if $d^i$ is positive, $e^i$ is feasible for $t^i$, and for all positive declarations of the other agents, all execution plans of the other agents, and every alternative strategy $(d'^i, e'^i)$ with $d'^i$ positive and $e'^i$ feasible for $t^i$, the utility of $(d^i,e^i)$ is at least that of $(d'^i,e'^i)$. The mechanism is **truthful** (Definition 19) if for every agent $i$ and every positive type $t^i$ there is a feasible execution plan $e^i$ such that $(t^i, e^i)$ — declaring the true type — is dominant.
--
--   **The replaced types.** For a type vector $t$, an allocation $o$ and a real number $M$, agent $i$'s type $t'^i = \operatorname{offOpt}(t,o,M,i)$ keeps $t^i_j$ on the tasks $j \in o^i$ and equals $M$ on every other task; $s = \operatorname{sType}(t,o,M)$ replaces every agent's type in this way. These are the types $t'^1$ and $s$ of the proof of Theorem 5.6, with $M$ standing for the paper's "$\infty$ (an arbitrary high value)".
--
--   These definitions are the setting of Theorem 5.6: replacing the optimal algorithm of the Compensation-and-Bonus mechanism by a non-optimal approximation algorithm destroys truthfulness.
--
--   **Formalization Note** Agents are `Fin n` with `[NeZero n]`, tasks `Fin k`, an allocation is a function `Fin k → Fin n`; both make-spans are `Finset.sup'` over the nonempty set of agents, so they are true maxima. An execution plan is a function of the allocation, so executions may depend on the mechanism's decision (Definition 18). The bonus uses the other agents' *declarations* and agent $i$'s own actual times (Definition 22). Positivity of declarations is required both of the strategy tested and of every alternative and of the others' declarations; the others' execution plans are arbitrary. The paper's $\infty$ is a real number $M$, not an extended real.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, pp. 175–176, Definition 10; p. 186, Definitions 18–19; p. 187, Definitions 20–22; p. 188, Definitions 23–24; p. 191, Definition 32; p. 192, proof of Theorem 5.6 (the types t′¹ and s)

import Mathlib

namespace AlgMechDesign.NonOptimal

open Finset

/-- A type vector `t` (Nisan–Ronen, Def. 10, pp. 175–176): `t i j` is the minimum time in which
agent `i : Fin n` can perform task `j : Fin k`. Types are positive. -/
def IsType {n k : ℕ} (t : Fin n → Fin k → ℝ) : Prop :=
  ∀ i j, 0 < t i j

/-- A single agent's type (or declaration) `tⁱ = (tⁱ_1, …, tⁱ_k)` is positive. -/
def IsAgentType {k : ℕ} (ti : Fin k → ℝ) : Prop :=
  ∀ j, 0 < ti j

/-- The load of agent `i` under the allocation `x : Fin k → Fin n` (task `j` goes to agent `x j`)
for the type vector `t`: `∑_{j ∈ xⁱ} tⁱ_j`. -/
def load {n k : ℕ} (t : Fin n → Fin k → ℝ) (x : Fin k → Fin n) (i : Fin n) : ℝ :=
  ∑ j ∈ univ.filter (fun j => x j = i), t i j

/-- The make-span `g(x, t) = maxᵢ ∑_{j ∈ xⁱ} tⁱ_j`, a maximum over the nonempty set of agents. -/
noncomputable def makespan {n k : ℕ} [NeZero n] (t : Fin n → Fin k → ℝ) (x : Fin k → Fin n) : ℝ :=
  univ.sup' univ_nonempty (load t x)

/-- `o` is an optimal allocation for the type vector `t`: its make-span is at most that of every
allocation. -/
def IsOptimalFor {n k : ℕ} [NeZero n] (t : Fin n → Fin k → ℝ) (o : Fin k → Fin n) : Prop :=
  ∀ y : Fin k → Fin n, makespan t o ≤ makespan t y

/-- Make-span of a vector of actual times `τ` (task `j` performed in time `τ j`) on the allocation
`x` (Def. 20): `g(x, τ) = maxₗ ∑_{j ∈ xˡ} τ_j`. -/
noncomputable def gT {n k : ℕ} [NeZero n] (x : Fin k → Fin n) (τ : Fin k → ℝ) : ℝ :=
  univ.sup' univ_nonempty (fun l => ∑ j ∈ univ.filter (fun j => x j = l), τ j)

/-- The corrected time vector for agent `i` (Def. 22): agent `i`'s own tasks at their actual times
`tt`, every other task `j ∈ xˡ` at the time `dˡ_j` declared by its agent `l`. -/
def corr {n k : ℕ} (i : Fin n) (x : Fin k → Fin n) (d : Fin n → Fin k → ℝ) (tt : Fin k → ℝ) :
    Fin k → ℝ :=
  fun j => if x j = i then tt j else d (x j) j

/-- `corr*(x, d)` (Def. 22): every task `j ∈ xˡ` at the time `dˡ_j` declared by its agent. -/
def corrStar {n k : ℕ} (x : Fin k → Fin n) (d : Fin n → Fin k → ℝ) : Fin k → ℝ :=
  fun j => d (x j) j

/-- An execution plan of an agent: for every decision (allocation) `x`, the actual time in which
it performs task `j` (only its own tasks, `x j = i`, matter). Executions may depend on the
decision (Def. 18). -/
abbrev ExecPlan (n k : ℕ) := (Fin k → Fin n) → Fin k → ℝ

/-- An execution plan `e` is feasible for agent `i` of true type `ti` (Def. 20): every task
allocated to `i` is performed in at least its true time, `t̃_j ≥ tⁱ_j`. -/
def FeasibleExec {n k : ℕ} (i : Fin n) (ti : Fin k → ℝ) (e : ExecPlan n k) : Prop :=
  ∀ (x : Fin k → Fin n) (j : Fin k), x j = i → ti j ≤ e x j

/-- The actual times of the outcome when the declarations are `d` and the agents' execution plans
are `E`: task `j` is performed by its agent `alloc d j` according to that agent's plan. -/
def actualTimes {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (d : Fin n → Fin k → ℝ) (E : Fin n → ExecPlan n k) : Fin k → ℝ :=
  fun j => E (alloc d j) (alloc d) j

/-- The compensation of agent `i` (Def. 21): `cⁱ(d, t̃) = ∑_{j ∈ xⁱ(d)} t̃_j`. -/
def compensation {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (d : Fin n → Fin k → ℝ) (tt : Fin k → ℝ) (i : Fin n) : ℝ :=
  ∑ j ∈ univ.filter (fun j => alloc d j = i), tt j

/-- The bonus of agent `i` (Def. 23): `bⁱ(d, t̃) = -g(x(d), corrⁱ(x(d), d, t̃))`. -/
noncomputable def bonus {n k : ℕ} [NeZero n] (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (d : Fin n → Fin k → ℝ) (tt : Fin k → ℝ) (i : Fin n) : ℝ :=
  -gT (alloc d) (corr i (alloc d) d tt)

/-- The Compensation-and-Bonus payment based on the allocation algorithm `alloc`
(Defs. 24 and 32): `pⁱ(d, t̃) = cⁱ(d, t̃) + bⁱ(d, t̃)`, the amount handed to agent `i`. -/
noncomputable def cbPay {n k : ℕ} [NeZero n] (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (d : Fin n → Fin k → ℝ) (tt : Fin k → ℝ) (i : Fin n) : ℝ :=
  compensation alloc d tt i + bonus alloc d tt i

/-- Utility of agent `i` in the Compensation-and-Bonus mechanism based on `alloc` when the
declarations are `d` and the execution plans are `E`: payment plus valuation
`vⁱ(x, t̃) = -∑_{j ∈ xⁱ} t̃_j` (Def. 20). -/
noncomputable def utility {n k : ℕ} [NeZero n] (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (d : Fin n → Fin k → ℝ) (E : Fin n → ExecPlan n k) (i : Fin n) : ℝ :=
  cbPay alloc d (actualTimes alloc d E) i -
    ∑ j ∈ univ.filter (fun j => alloc d j = i), actualTimes alloc d E j

/-- The strategy `(di, ei)` is dominant for agent `i` of true type `ti` in the
Compensation-and-Bonus mechanism based on `alloc`: `di` is positive, `ei` is feasible for `ti`, and
for all positive declarations of the others, all execution plans of the others (arbitrary), and
every alternative strategy `(di', ei')` with `di'` positive and `ei'` feasible for `ti`, the
utility of `(di, ei)` is at least that of `(di', ei')`. -/
def Dominant {n k : ℕ} [NeZero n] (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) (i : Fin n)
    (ti di : Fin k → ℝ) (ei : ExecPlan n k) : Prop :=
  IsAgentType di ∧ FeasibleExec i ti ei ∧
    ∀ d : Fin n → Fin k → ℝ, IsType d → ∀ E : Fin n → ExecPlan n k,
      ∀ di' : Fin k → ℝ, IsAgentType di' → ∀ ei' : ExecPlan n k, FeasibleExec i ti ei' →
        utility alloc (Function.update d i di') (Function.update E i ei') i ≤
          utility alloc (Function.update d i di) (Function.update E i ei) i

/-- Truthfulness of the Compensation-and-Bonus mechanism based on `alloc` (Def. 19): for every
agent `i` and every positive type `ti` there is an execution plan `ei`, feasible for `ti`, such
that the strategy `(ti, ei)` (declare the true type) is dominant. -/
def Truthful {n k : ℕ} [NeZero n] (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) : Prop :=
  ∀ (i : Fin n) (ti : Fin k → ℝ), IsAgentType ti →
    ∃ ei : ExecPlan n k, FeasibleExec i ti ei ∧ Dominant alloc i ti ti ei

/-- The type of agent `i` that keeps `tⁱ_j` on the tasks `j ∈ oⁱ` the allocation `o` gives to `i`
and puts the large value `M` (the paper's "∞") on every other task (proof of Theorem 5.6,
p. 192). -/
def offOpt {n k : ℕ} (t : Fin n → Fin k → ℝ) (o : Fin k → Fin n) (M : ℝ) (i : Fin n) :
    Fin k → ℝ :=
  fun j => if o j = i then t i j else M

/-- The type vector `s` of Corollary 5.8: every agent's type replaced by `offOpt t o M i`. -/
def sType {n k : ℕ} (t : Fin n → Fin k → ℝ) (o : Fin k → Fin n) (M : ℝ) :
    Fin n → Fin k → ℝ :=
  fun i => offOpt t o M i

end AlgMechDesign.NonOptimal


