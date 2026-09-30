-- Prove2me | Definitions.Def_AlgMechDesign_Rounding_Model
-- name    : AlgMechDesign_Rounding_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T21:57:54.527559+00:00
-- url     : https://prove2.me/theorems/62ecfb2a-d353-4881-b10e-b86c0cefc5fc
-- title:
--   Bounded task scheduling with verification: bounded types, make-span, corrected times, rounding, dominance, truthfulness
-- statement:
--   This file fixes the model of **task scheduling with verification** (Nisan–Ronen, Definitions 18–22) on the **bounded** type space of Definition 33, together with the rounding operation of §5.6.
--
--   There are $n$ agents $i \in \{1,\dots,n\}$ and $k$ tasks $j \in \{1,\dots,k\}$. A **type vector** $t = (t^i_j)$ records the time $t^i_j$ agent $i$ needs for task $j$. In the bounded problem there are fixed numbers $0 < a < b$ and every entry satisfies $a \le t^i_j \le b$; the same bound applies to every declaration an agent may make. An **allocation** $x$ assigns each task $j$ to one agent; $x^i$ is the set of tasks of agent $i$.
--
--   1. The **make-span** of $x$ under $t$ is $g(x,t) = \max_i \sum_{j \in x^i} t^i_j$. For a vector of actual times $\tilde t = (\tilde t_1,\dots,\tilde t_k)$ the make-span is $g(x,\tilde t) = \max_i \sum_{j\in x^i} \tilde t_j$.
--   2. The **corrected time vector** of agent $i$ under declarations $d$ and actual times $\tilde t$ is
--   $$\mathrm{corr}^i(x,d,\tilde t)_j = \begin{cases} \tilde t_j & j \in x^i,\\ d^l_j & j \in x^l,\ l\neq i,\end{cases}$$
--   and $\mathrm{corr}^*(x,d)_j = d^l_j$ for $j \in x^l$.
--   3. **Rounding**: for a step $\delta > 0$, $\hat r = \delta \lceil r/\delta \rceil$ is $r$ rounded up to an integer multiple of $\delta$; vectors and type vectors are rounded entrywise.
--   4. A **strategy** of agent $i$ is a declaration $d^i \in [a,b]^k$ together with an **execution plan**: for every decision $x$ of the mechanism, the actual time in which it performs each of its tasks. The plan is **feasible** for the true type $t^i$ if every own task $j$ is performed in time $\tilde t_j \ge t^i_j$; there is no upper bound on actual times.
--   5. The mechanism's allocation depends on the declarations only; the payment $p^i$ handed to agent $i$ depends on the declarations and on the actual times. Agent $i$'s **utility** is $p^i - \sum_{j\in x^i}\tilde t_j$ (payment plus valuation).
--   6. A strategy is **dominant** for agent $i$ of type $t^i$ if, against every declarations in $[a,b]$ and every executions of the other agents, it yields at least the utility of every other strategy of agent $i$ (declaration in $[a,b]^k$, execution feasible for $t^i$). The mechanism is **truthful** (Definition 19) if for every agent and every type in $[a,b]^k$ some strategy that declares the true type is dominant.
--
--   These objects are shared by every statement of the mission about the rounding mechanism.
--
--   **Formalization Note** Agents are `Fin n`, tasks `Fin k`, allocations are functions `Fin k → Fin n`, and the make-span is a `Finset.sup'` over the nonempty set of agents (`[NeZero n]`). `roundUp δ r = δ * ⌈r / δ⌉` uses `Int.ceil`. An execution plan is a function from allocations to time vectors, so executions may depend on the decision (Definition 18). The others' executions in the dominance quantifier are arbitrary real vectors.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, pp. 186–187, Definitions 18–20; p. 187, Definition 22; p. 192, Definition 33 and Notation

import Mathlib

namespace AlgMechDesign.Rounding

open Finset

/-- A type vector (or declaration profile) `t` of the bounded scheduling problem (Nisan–Ronen,
Def. 33, p. 192): `t i j` is the time agent `i : Fin n` needs for task `j : Fin k`, and every
entry lies in the fixed interval `[a, b]`. -/
def IsBoundedType {n k : ℕ} (a b : ℝ) (t : Fin n → Fin k → ℝ) : Prop :=
  ∀ i j, a ≤ t i j ∧ t i j ≤ b

/-- A single agent's type (or declaration) `tⁱ = (tⁱ_1, …, tⁱ_k)` has every entry in `[a, b]`. -/
def IsBoundedAgentType {k : ℕ} (a b : ℝ) (ti : Fin k → ℝ) : Prop :=
  ∀ j, a ≤ ti j ∧ ti j ≤ b

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

/-- Rounding up to an integer multiple of `δ` (Notation, p. 192): `r̂ = δ ⌈r / δ⌉`. -/
noncomputable def roundUp (δ r : ℝ) : ℝ :=
  δ * (⌈r / δ⌉ : ℤ)

/-- Entrywise rounding of a vector of times `τ : Fin k → ℝ` (the paper's `τ̂`). -/
noncomputable def roundVec {k : ℕ} (δ : ℝ) (τ : Fin k → ℝ) : Fin k → ℝ :=
  fun j => roundUp δ (τ j)

/-- Entrywise rounding of a type vector (declaration profile) `t` (the paper's `t̂`). -/
noncomputable def roundType {n k : ℕ} (δ : ℝ) (t : Fin n → Fin k → ℝ) : Fin n → Fin k → ℝ :=
  fun i j => roundUp δ (t i j)

/-- An execution plan of an agent: for every decision (allocation) `x`, the actual time in which
it performs task `j` (only its own tasks, `x j = i`, matter). Executions may depend on the
decision (Def. 18). -/
abbrev ExecPlan (n k : ℕ) := (Fin k → Fin n) → Fin k → ℝ

/-- An execution plan `e` is feasible for agent `i` of true type `ti` (Def. 20): every task
allocated to `i` is performed in at least its true time, `t̃_j ≥ tⁱ_j`. There is no upper bound
on actual times. -/
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
verification `(alloc, pay)` on the bounded type space `[a, b]` (Defs. 3, 18, 33): `di` is a
declaration in `[a, b]`, `ei` is feasible for `ti`, and for all declarations of the others in
`[a, b]`, all execution plans of the others, and every alternative strategy `(di', ei')` with
`di'` in `[a, b]` and `ei'` feasible for `ti`, the utility of `(di, ei)` is at least that of
`(di', ei')`. -/
def Dominant {n k : ℕ} (a b : ℝ) (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → (Fin k → ℝ) → Fin n → ℝ) (i : Fin n)
    (ti di : Fin k → ℝ) (ei : ExecPlan n k) : Prop :=
  IsBoundedAgentType a b di ∧ FeasibleExec i ti ei ∧
    ∀ d : Fin n → Fin k → ℝ, IsBoundedType a b d → ∀ E : Fin n → ExecPlan n k,
      ∀ di' : Fin k → ℝ, IsBoundedAgentType a b di' → ∀ ei' : ExecPlan n k,
        FeasibleExec i ti ei' →
          utility alloc pay (Function.update d i di') (Function.update E i ei') i ≤
            utility alloc pay (Function.update d i di) (Function.update E i ei) i

/-- Truthfulness of a mechanism with verification on the bounded type space (Def. 19): for every
agent `i` and every type `ti` in `[a, b]` there is an execution plan `ei` such that the strategy
`(ti, ei)` (declare the true type) is dominant. -/
def Truthful {n k : ℕ} (a b : ℝ) (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → (Fin k → ℝ) → Fin n → ℝ) : Prop :=
  ∀ (i : Fin n) (ti : Fin k → ℝ), IsBoundedAgentType a b ti →
    ∃ ei : ExecPlan n k, Dominant a b alloc pay i ti ti ei

end AlgMechDesign.Rounding


