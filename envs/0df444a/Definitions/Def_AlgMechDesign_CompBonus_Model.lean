-- Prove2me | Definitions.Def_AlgMechDesign_CompBonus_Model
-- name    : AlgMechDesign_CompBonus_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T20:54:57.767+00:00
-- url     : https://prove2.me/theorems/15d3d361-ebce-4bdb-99ef-8433c805bf98
-- title:
--   Task scheduling with verification: declarations, execution plans, dominant strategies, strong truthfulness, participation
-- statement:
--   This file fixes the task scheduling problem with verification of Nisan and Ronen (Definitions 10, 18, 19, 20 and 28) and the incentive notions used with it.
--
--   There are $k$ tasks $j \in \{1,\dots,k\}$ and $n$ agents $i \in \{1,\dots,n\}$. A **type vector** $t = (t^1,\dots,t^n)$ records the minimum time $t^i_j > 0$ in which agent $i$ can perform task $j$. An **allocation** $x$ gives each task $j$ to one agent $x(j)$; $x^i = \{j : x(j) = i\}$ is the (possibly empty) set of tasks of agent $i$. The make-span of $x$ under $t$, and the make-span of $x$ under a vector $\tilde t = (\tilde t_1,\dots,\tilde t_k)$ of actual execution times, are
--   $$
--   g(x,t) = \max_{1\le i\le n} \sum_{j\in x^i} t^i_j, \qquad g(x,\tilde t) = \max_{1\le l\le n} \sum_{j \in x^l} \tilde t_j .
--   $$
--   Given declarations $d$ and actual times $\tilde t$, the **corrected time vector** for agent $i$ is $\mathrm{corr}^i(x,d,\tilde t)_j = \tilde t_j$ for $j \in x^i$ and $d^l_j$ for $j \in x^l$, $l \ne i$; and $\mathrm{corr}^*(x,d)_j = d^l_j$ for $j \in x^l$.
--
--   A **mechanism with verification** is a pair $(x, p)$: an allocation rule $x(d)$ that depends on the declarations $d$ only, and payments $p^i(d, \tilde t)$ (handed to agent $i$) that depend on the declarations and on the actual times. A strategy of agent $i$ is a declaration $d^i$ together with an **execution plan** $e^i$, which for every allocation $x$ gives the actual time $e^i(x)_j$ of each task $j \in x^i$; it is feasible for an agent of type $t^i$ if $e^i(x)_j \ge t^i_j$ whenever $j \in x^i$. When the declarations are $d$ and the plans are $e^1,\dots,e^n$, the output is $x = x(d)$ with actual times $\tilde t_j = e^{x(j)}(x)_j$, and agent $i$'s utility is
--   $$
--   u^i = p^i(d,\tilde t) - \sum_{j\in x^i(d)} \tilde t_j .
--   $$
--
--   1. A strategy $(d^i, e^i)$, with $d^i$ positive and $e^i$ feasible for $t^i$, is **dominant** for agent $i$ of type $t^i$ if, for all positive declarations of the other agents, all execution plans of the other agents, and every alternative strategy $(d'^i, e'^i)$ with $d'^i$ positive and $e'^i$ feasible for $t^i$, it gives agent $i$ at least the utility of the alternative.
--   2. The mechanism is **truthful** (Definition 19) if for every agent $i$ and every positive type $t^i$ some strategy of the form $(t^i, e^i)$ is dominant.
--   3. It is **strongly truthful** if moreover every dominant strategy $(d^i, e^i)$ of an agent of type $t^i$ has $d^i = t^i$ and performs every allocated task in minimal time, $e^i(x)_j = t^i_j$ for all $x$ and $j \in x^i$.
--   4. An allocation rule is an **optimal allocation algorithm** if $g(x(d), d) \le g(y, d)$ for every positive $d$ and every allocation $y$ (ties are broken arbitrarily).
--   5. The mechanism **implements the optimum** if, for every positive true type vector $t$ and every profile of strategies each dominant for its agent's true type, the output satisfies $g(x, \tilde t) \le g(y, t)$ for every allocation $y$.
--   6. It satisfies **participation constraints** (Definition 28) if for every positive $t$, every $\tilde t$ and every agent $i$ with $\tilde t_j = t^i_j$ for all $j \in x^i(t)$, one has $p^i(t,\tilde t) - \sum_{j \in x^i(t)} \tilde t_j \ge 0$.
--
--   These notions are the vocabulary of §5 of the paper: Theorem 5.1 and Theorem 5.4 are stated with them.
--
--   **Formalization Note** Agents are `Fin n`, tasks `Fin k`, allocations functions `Fin k → Fin n`; both make-spans are `Finset.sup'` over the nonempty set of agents (`[NeZero n]`), so they are true maxima. Declarations range over positive vectors, the type space of Definition 10 (Definition 18's "unrestricted" declaration is any element of it). The execution plan sees the decision $x$, as Definition 18 allows ("$e^i$ may depend on $t^i$ as well as on $k$"). In the dominance quantifier the other agents' execution plans are arbitrary real-valued plans, a superset of the plans feasible for some positive type. Strong truthfulness constrains both the declaration and the execution, as in the proof of Theorem 5.1 ("the only dominant strategy for each agent is to reveal its true type and to execute its tasks in minimal time").
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, pp. 171–172, Definitions 3, 4, 5; pp. 175–176, Definition 10; p. 186, Definitions 18, 19; p. 187, Definitions 20, 22; p. 188, proof of Theorem 5.1; p. 189, Definition 28

import Mathlib

namespace AlgMechDesign.CompBonus

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

/-- The make-span `g(x, t) = maxᵢ ∑_{j ∈ xⁱ} tⁱ_j` (Def. 10), a maximum over the nonempty set of
agents. -/
noncomputable def makespan {n k : ℕ} [NeZero n] (t : Fin n → Fin k → ℝ) (x : Fin k → Fin n) : ℝ :=
  univ.sup' univ_nonempty (load t x)

/-- Make-span of a vector of actual times `τ` (task `j` performed in time `τ j`) on the allocation
`x` (Def. 20): `g(x, τ) = maxₗ ∑_{j ∈ xˡ} τ_j`. -/
noncomputable def gT {n k : ℕ} [NeZero n] (x : Fin k → Fin n) (τ : Fin k → ℝ) : ℝ :=
  univ.sup' univ_nonempty (fun l => ∑ j ∈ univ.filter (fun j => x j = l), τ j)

/-- The corrected time vector for agent `i` (Def. 22): agent `i`'s own tasks at their actual times
`tt`, every other task `j ∈ xˡ` (`l ≠ i`) at the time `dˡ_j` declared by its agent `l`. -/
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
are `E`: task `j` is performed by its agent `alloc d j` according to that agent's plan, which
sees the decision `alloc d`. -/
def actualTimes {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (d : Fin n → Fin k → ℝ) (E : Fin n → ExecPlan n k) : Fin k → ℝ :=
  fun j => E (alloc d j) (alloc d) j

/-- Utility of agent `i` in the mechanism with verification `(alloc, pay)` (Def. 20): the
allocation `x = alloc d` depends on the declarations only, the payment `pay d t̃ i` (the amount
handed to agent `i`) on the declarations and the actual times, and the valuation is
`vⁱ(x, t̃) = -∑_{j ∈ xⁱ} t̃_j`. -/
def utility {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → (Fin k → ℝ) → Fin n → ℝ)
    (d : Fin n → Fin k → ℝ) (E : Fin n → ExecPlan n k) (i : Fin n) : ℝ :=
  pay d (actualTimes alloc d E) i -
    ∑ j ∈ univ.filter (fun j => alloc d j = i), actualTimes alloc d E j

/-- The strategy `(di, ei)` is dominant for agent `i` of true type `ti` in the mechanism with
verification `(alloc, pay)` (Defs. 3, 18): `di` is a positive declaration, `ei` is feasible for
`ti`, and for all positive declarations of the others, all execution plans of the others, and
every alternative strategy `(di', ei')` with `di'` positive and `ei'` feasible for `ti`, the
utility of `(di, ei)` is at least that of `(di', ei')`. -/
def Dominant {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → (Fin k → ℝ) → Fin n → ℝ) (i : Fin n)
    (ti di : Fin k → ℝ) (ei : ExecPlan n k) : Prop :=
  IsAgentType di ∧ FeasibleExec i ti ei ∧
    ∀ d : Fin n → Fin k → ℝ, IsType d → ∀ E : Fin n → ExecPlan n k,
      ∀ di' : Fin k → ℝ, IsAgentType di' → ∀ ei' : ExecPlan n k, FeasibleExec i ti ei' →
        utility alloc pay (Function.update d i di') (Function.update E i ei') i ≤
          utility alloc pay (Function.update d i di) (Function.update E i ei) i

/-- Truthfulness of a mechanism with verification (Def. 19): for every agent `i` and every
positive type `ti` there is an execution plan `ei` such that the strategy `(ti, ei)` (declare the
true type) is dominant. -/
def Truthful {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → (Fin k → ℝ) → Fin n → ℝ) : Prop :=
  ∀ (i : Fin n) (ti : Fin k → ℝ), IsAgentType ti → ∃ ei : ExecPlan n k, Dominant alloc pay i ti ti ei

/-- Strong truthfulness of a mechanism with verification (Def. 19 and the proof of Theorem 5.1):
it is truthful, and every dominant strategy `(di, ei)` of an agent `i` of positive type `ti` is to
declare the true type, `di = ti`, and to perform every task allocated to `i` in minimal time,
`ei x j = tⁱ_j` whenever `x j = i`. -/
def StronglyTruthful {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → (Fin k → ℝ) → Fin n → ℝ) : Prop :=
  Truthful alloc pay ∧
    ∀ (i : Fin n) (ti : Fin k → ℝ), IsAgentType ti →
      ∀ (di : Fin k → ℝ) (ei : ExecPlan n k), Dominant alloc pay i ti di ei →
        di = ti ∧ ∀ (x : Fin k → Fin n) (j : Fin k), x j = i → ei x j = ti j

/-- `alloc` is an optimal allocation algorithm: on every positive declaration profile `d` its
allocation has the least make-span `g(·, d)` among all allocations. Ties are arbitrary. -/
def IsOptimalAlloc {n k : ℕ} [NeZero n] (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) :
    Prop :=
  ∀ d : Fin n → Fin k → ℝ, IsType d → ∀ y : Fin k → Fin n, makespan d (alloc d) ≤ makespan d y

/-- The mechanism with verification `(alloc, pay)` implements the (exact) task scheduling problem
with dominant strategies (Def. 3, second bullet): for every positive true type vector `t` and every
profile of strategies `(D l, E l)` each dominant for its agent's true type, the output
`(x, t̃) = (alloc D, actual times)` has make-span `g(x, t̃)` at most the optimal make-span
`g(y, t)` of every allocation `y`. -/
def ImplementsOptimum {n k : ℕ} [NeZero n] (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → (Fin k → ℝ) → Fin n → ℝ) : Prop :=
  ∀ t : Fin n → Fin k → ℝ, IsType t →
    ∀ (D : Fin n → Fin k → ℝ) (E : Fin n → ExecPlan n k),
      (∀ l : Fin n, Dominant alloc pay l (t l) (D l) (E l)) →
        ∀ y : Fin k → Fin n, gT (alloc D) (actualTimes alloc D E) ≤ makespan t y

/-- Participation constraints (Def. 28): for every positive declaration profile `t`, every vector
of actual times `t̃` and every agent `i`, if agent `i` performed each of its tasks
`j ∈ xⁱ(t)` in exactly its declared time `t̃_j = tⁱ_j`, then its utility
`pⁱ(t, t̃) + vⁱ(x(t), t̃)` is non-negative. -/
def Participation {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → (Fin k → ℝ) → Fin n → ℝ) : Prop :=
  ∀ t : Fin n → Fin k → ℝ, IsType t → ∀ (tt : Fin k → ℝ) (i : Fin n),
    (∀ j, alloc t j = i → tt j = t i j) →
      0 ≤ pay t tt i - ∑ j ∈ univ.filter (fun j => alloc t j = i), tt j

end AlgMechDesign.CompBonus


