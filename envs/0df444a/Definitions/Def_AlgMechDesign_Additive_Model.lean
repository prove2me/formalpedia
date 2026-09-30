-- Prove2me | Definitions.Def_AlgMechDesign_Additive_Model
-- name    : AlgMechDesign_Additive_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T19:03:52.979721+00:00
-- url     : https://prove2.me/theorems/25e28ce2-c5f2-4ecd-9792-ec63d9ed4bea
-- title:
--   Task scheduling on unrelated machines: types, allocations, make-span, truthful mechanisms, c-approximation
-- statement:
--   This file sets up the **task scheduling problem** of Nisan and Ronen (Definition 10) and the direct mechanisms that solve it.
--
--   There are $n$ agents (machines) $i \in \{1,\dots,n\}$ and $k$ tasks $j \in \{1,\dots,k\}$. The **type** of agent $i$ is a vector $t^i = (t^i_1,\dots,t^i_k)$ of positive reals, $t^i_j$ being the minimum time in which agent $i$ can perform task $j$; a **type vector** $t = (t^1,\dots,t^n)$ collects all agents' types, and all its entries are positive.
--
--   An **allocation** assigns every task to one agent; $x^i$ denotes the set of tasks given to agent $i$, so $x = (x^1,\dots,x^n)$ is a partition of the tasks (parts may be empty). The time agent $i$ spends is $t^i(x^i) = \sum_{j \in x^i} t^i_j$, its valuation is $v^i(x,t^i) = -t^i(x^i)$, and the **make-span** (the objective) is
--
--   $$g(x,t) = \max_{1\le i\le n} \sum_{j\in x^i} t^i_j .$$
--
--   A **direct mechanism** $m = (x,p)$ consists of an allocation rule $t \mapsto x(t)$ and payments $t \mapsto p^i(t)$ handed to each agent. When the declared type vector is $d$ and agent $i$'s true type is $t^i$, agent $i$'s utility is $u^i = p^i(d) - t^i(x^i(d))$. The mechanism is **truthful** (Definition 4) if for every positive declaration vector $d$, every agent $i$, every positive true type $t^i$ and every positive misreport $t'^i$,
--
--   $$p^i(t^i,d^{-i}) - t^i\bigl(x^i(t^i,d^{-i})\bigr) \;\ge\; p^i(t'^i,d^{-i}) - t^i\bigl(x^i(t'^i,d^{-i})\bigr).$$
--
--   The allocation rule is a **$c$-approximation** (Definition 2) if $g(x(t),t) \le c\, g(y,t)$ for every positive type vector $t$ and every allocation $y$.
--
--   These are the objects about which the lower bound for additive mechanisms (Theorem 4.10) is stated.
--
--   **Formalization Note** Agents are `Fin n`, tasks `Fin k`, and an allocation is a function `Fin k → Fin n` sending each task to its agent; `taskSet x i` is $x^i$. The make-span is a `Finset.sup'` over the nonempty set of agents (`[NeZero n]`), so it is the true maximum. Truthfulness and approximation quantify over positive types only; the mechanism's values on non-positive inputs are irrelevant.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, pp. 171–172, Definitions 2 and 4; pp. 175–176, Definition 10 and the Notation paragraph of §4.1

import Mathlib

namespace AlgMechDesign.Additive

open Finset

/-- A type vector `t` (Nisan–Ronen, Def. 10, pp. 175–176): `t i j` is the minimum time in which
agent `i : Fin n` can perform task `j : Fin k`. Types are positive. -/
def IsType {n k : ℕ} (t : Fin n → Fin k → ℝ) : Prop :=
  ∀ i j, 0 < t i j

/-- A single agent's type `tⁱ = (tⁱ_1, …, tⁱ_k)` is positive. -/
def IsAgentType {k : ℕ} (ti : Fin k → ℝ) : Prop :=
  ∀ j, 0 < ti j

/-- The set `xⁱ` of tasks that the allocation `x : Fin k → Fin n` (task `j` goes to agent `x j`)
gives to agent `i`. -/
def taskSet {n k : ℕ} (x : Fin k → Fin n) (i : Fin n) : Finset (Fin k) :=
  univ.filter (fun j => x j = i)

/-- The load of agent `i` under the allocation `x`: `tⁱ(xⁱ) = ∑_{j ∈ xⁱ} tⁱ_j`. Agent `i`'s
valuation is `-load t x i`. -/
def load {n k : ℕ} (t : Fin n → Fin k → ℝ) (x : Fin k → Fin n) (i : Fin n) : ℝ :=
  ∑ j ∈ taskSet x i, t i j

/-- The make-span `g(x, t) = maxᵢ ∑_{j ∈ xⁱ} tⁱ_j`, a maximum over the nonempty set of agents. -/
noncomputable def makespan {n k : ℕ} [NeZero n] (t : Fin n → Fin k → ℝ) (x : Fin k → Fin n) : ℝ :=
  univ.sup' univ_nonempty (load t x)

/-- Quasi-linear utility of agent `i` with true type `ti` in the direct mechanism
`(alloc, pay)` when the declaration profile is `d`: the payment handed to the agent minus the
true time it spends on the tasks allocated to it. -/
def utility {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (d : Fin n → Fin k → ℝ) (i : Fin n)
    (ti : Fin k → ℝ) : ℝ :=
  pay d i - ∑ j ∈ taskSet (alloc d) i, ti j

/-- Truthfulness (Def. 4): for every positive declaration profile, every agent, every positive
true type and every positive misreport, reporting the true type gives at least the utility of
the misreport. -/
def IsTruthful {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) : Prop :=
  ∀ d : Fin n → Fin k → ℝ, IsType d → ∀ i : Fin n, ∀ ti ti' : Fin k → ℝ,
    IsAgentType ti → IsAgentType ti' →
      utility alloc pay (Function.update d i ti') i ti ≤
        utility alloc pay (Function.update d i ti) i ti

/-- `c`-approximation (Def. 2): on every positive type vector the chosen allocation has
make-span at most `c` times that of every allocation. -/
def IsApprox {n k : ℕ} [NeZero n] (c : ℝ) (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) :
    Prop :=
  ∀ t : Fin n → Fin k → ℝ, IsType t → ∀ y : Fin k → Fin n,
    makespan t (alloc t) ≤ c * makespan t y

end AlgMechDesign.Additive


