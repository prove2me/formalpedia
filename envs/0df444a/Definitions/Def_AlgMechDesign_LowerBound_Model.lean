-- Prove2me | Definitions.Def_AlgMechDesign_LowerBound_Model
-- name    : AlgMechDesign_LowerBound_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T18:32:02.428589+00:00
-- url     : https://prove2.me/theorems/f489990d-8cd2-443f-8bd2-c33bfae20a5f
-- title:
--   Task scheduling: positive types, allocations, make-span, direct mechanisms, truthfulness, c-approximation
-- statement:
--   This file fixes the task scheduling model of Nisan and Ronen (Definition 10) and the notions of a direct mechanism for it.
--
--   There are $n$ agents $i \in \{1,\dots,n\}$ and $k$ tasks $j \in \{1,\dots,k\}$. A **type vector** $t = (t^1,\dots,t^n)$ records, for every agent $i$ and task $j$, the time $t^i_j > 0$ agent $i$ needs to perform task $j$. An **allocation** $x$ assigns each task to one agent; $x^i$ denotes the set of tasks given to agent $i$ (possibly empty). For a set $X$ of tasks write $t^i(X) = \sum_{j\in X} t^i_j$. The **load** of agent $i$ is $t^i(x^i)$, its valuation is $-t^i(x^i)$, and the **make-span** is
--
--   $$
--   g(x,t) = \max_{1\le i\le n} \sum_{j \in x^i} t^i_j .
--   $$
--
--   A **direct mechanism** $m = (x, p)$ consists of an allocation rule $t \mapsto x(t)$ and payments $t \mapsto p^i(t)$ handed to each agent. When the declared types are $d$ and agent $i$'s true type is $t^i$, agent $i$'s (quasi-linear) utility is $p^i(d) - t^i(x^i(d))$.
--
--   1. The mechanism is **truthful** (Definition 4) if, for every positive declaration profile $d$, every agent $i$, every positive true type $t^i$ and every positive misreport $t'^i$, agent $i$'s utility when declaring $t^i$ (the others declaring $d^{-i}$) is at least its utility when declaring $t'^i$.
--   2. The allocation rule is a **$c$-approximation** (Definition 2) if $g(x(t),t) \le c\cdot g(y,t)$ for every positive type vector $t$ and every allocation $y$.
--
--   These are the objects about which the lower bound of Theorem 4.6 is proved after the reduction to truthful mechanisms.
--
--   **Formalization Note** Agents are `Fin n`, tasks `Fin k`, and an allocation is a function `Fin k → Fin n` sending each task to its agent. The make-span is a finite maximum and requires $n \ge 1$ (`NeZero n`). All types and misreports are required to be strictly positive, as in Definition 10 (times are positive real numbers). Payments are real numbers of either sign.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, pp. 171-172 (Definitions 2 and 4), pp. 175-176 (Definition 10 and the Notation after it), p. 178 (Notation t^i(X))

import Mathlib

namespace AlgMechDesign.LowerBound

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

/-- The time `tⁱ(X) = ∑_{j ∈ X} tⁱ_j` an agent of type `ti` needs to perform all tasks of `X`
(Notation, p. 178). -/
def taskTime {k : ℕ} (ti : Fin k → ℝ) (X : Finset (Fin k)) : ℝ :=
  ∑ j ∈ X, ti j

/-- The load of agent `i` under the allocation `x`: `tⁱ(xⁱ) = ∑_{j ∈ xⁱ} tⁱ_j`. Agent `i`'s
valuation is `-load t x i`. -/
def load {n k : ℕ} (t : Fin n → Fin k → ℝ) (x : Fin k → Fin n) (i : Fin n) : ℝ :=
  taskTime (t i) (taskSet x i)

/-- The make-span `g(x, t) = maxᵢ ∑_{j ∈ xⁱ} tⁱ_j`, a maximum over the nonempty set of agents. -/
noncomputable def makespan {n k : ℕ} [NeZero n] (t : Fin n → Fin k → ℝ) (x : Fin k → Fin n) : ℝ :=
  univ.sup' univ_nonempty (load t x)

/-- Quasi-linear utility of agent `i` with true type `ti` in the direct mechanism
`(alloc, pay)` when the declaration profile is `d`: the payment handed to the agent minus the
true time it spends on the tasks allocated to it. -/
def utility {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (d : Fin n → Fin k → ℝ) (i : Fin n)
    (ti : Fin k → ℝ) : ℝ :=
  pay d i - taskTime ti (taskSet (alloc d) i)

/-- Truthfulness (Def. 4) of a direct mechanism: for every positive declaration profile, every
agent, every positive true type and every positive misreport, reporting the true type gives at
least the utility of the misreport. -/
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

end AlgMechDesign.LowerBound


