-- Prove2me | Definitions.Def_AlgMechDesign_MinWork_Model
-- name    : AlgMechDesign_MinWork_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T18:07:13.323258+00:00
-- url     : https://prove2.me/theorems/1554da8f-f796-483c-8812-0a3ba789b45c
-- title:
--   Task scheduling on unrelated machines: types, allocations, make-span, truthful and approximate mechanisms
-- statement:
--   This file fixes the task allocation problem of Nisan and Ronen (Definition 10) and the incentive notions of their §2 (Definitions 2, 4, 5).
--
--   There are $k$ tasks $j \in \{1,\dots,k\}$ and $n$ agents $i \in \{1,\dots,n\}$. A **type vector** $t = (t^1,\dots,t^n)$ records, for each agent $i$ and task $j$, the time $t^i_j$ agent $i$ needs to perform task $j$; types are positive, $t^i_j > 0$. An **allocation** $x$ assigns each task $j$ to one agent $x(j)$; the set of tasks of agent $i$ is $x^i = \{j : x(j) = i\}$ (possibly empty). The **load** of agent $i$ and the **make-span** are
--   $$
--   t^i(x^i) = \sum_{j \in x^i} t^i_j, \qquad g(x,t) = \max_{1 \le i \le n} \sum_{j \in x^i} t^i_j ,
--   $$
--   and agent $i$'s valuation of $x$ is $v^i(x,t^i) = -t^i(x^i)$.
--
--   A **direct mechanism** is a pair $(x, p)$ of an allocation rule $x(d)$ and payments $p^i(d)$ computed from the declared type vector $d$; $p^i$ is the amount handed to agent $i$. Agent $i$ with true type $t^i$ has quasi-linear utility $u^i = p^i(d) - \sum_{j \in x^i(d)} t^i_j$ when the declarations are $d$.
--
--   1. The mechanism is **truthful** if for every positive declaration profile $d^{-i}$ of the others, every positive true type $t^i$ and every positive misreport $d^i$, declaring $t^i$ gives agent $i$ at least the utility of declaring $d^i$.
--   2. It is **strongly truthful** if it is truthful and every positive misreport $d^i \neq t^i$ gives agent $i$ strictly smaller utility than the truth for at least one positive profile $d^{-i}$ of the others.
--   3. The allocation rule is a **$c$-approximation** if for every positive type vector $t$ and every allocation $y$, $g(x(t),t) \le c \cdot g(y,t)$.
--
--   These notions are the vocabulary of the MinWork mission: Theorem 4.1 is stated with them.
--
--   **Formalization Note** Agents are `Fin n`, tasks `Fin k`, allocations functions `Fin k → Fin n`. The make-span is a `Finset.sup'` over the nonempty set of agents, so it needs `n ≥ 1` (`[NeZero n]`) and is always the true maximum. Given truthfulness, "every misreport is strictly worse for some declarations of the others" is exactly the paper's "truth-telling is the only dominant strategy" (Definition 5).
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, pp. 171–172, Definitions 2, 3, 4, 5; pp. 175–176, Definition 10 and Notation

import Mathlib

namespace AlgMechDesign.MinWork

open Finset

/-- A type vector `t` (Nisan–Ronen, Def. 10, pp. 175–176): `t i j` is the minimum time in which
agent `i : Fin n` can perform task `j : Fin k`. Types are positive. -/
def IsType {n k : ℕ} (t : Fin n → Fin k → ℝ) : Prop :=
  ∀ i j, 0 < t i j

/-- A single agent's type `tⁱ = (tⁱ_1, …, tⁱ_k)` is positive. -/
def IsAgentType {k : ℕ} (ti : Fin k → ℝ) : Prop :=
  ∀ j, 0 < ti j

/-- The load of agent `i` under the allocation `x : Fin k → Fin n` (task `j` goes to agent `x j`):
`tⁱ(xⁱ) = ∑_{j ∈ xⁱ} tⁱ_j`. Agent `i`'s valuation is `-load t x i`. -/
def load {n k : ℕ} (t : Fin n → Fin k → ℝ) (x : Fin k → Fin n) (i : Fin n) : ℝ :=
  ∑ j ∈ univ.filter (fun j => x j = i), t i j

/-- The make-span `g(x, t) = maxᵢ ∑_{j ∈ xⁱ} tⁱ_j`, a maximum over the nonempty set of agents. -/
noncomputable def makespan {n k : ℕ} [NeZero n] (t : Fin n → Fin k → ℝ) (x : Fin k → Fin n) : ℝ :=
  univ.sup' univ_nonempty (load t x)

/-- Quasi-linear utility of agent `i` with true type `ti` in the direct mechanism
`(alloc, pay)` when the declaration profile is `d`: the payment handed to the agent minus the
true time it spends on the tasks allocated to it. -/
def utility {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (d : Fin n → Fin k → ℝ) (i : Fin n)
    (ti : Fin k → ℝ) : ℝ :=
  pay d i - ∑ j ∈ univ.filter (fun j => alloc d j = i), ti j

/-- Truthfulness (Def. 4): for every positive declaration profile of the others, every agent,
every positive true type and every positive misreport, reporting the true type gives at least
the utility of the misreport. -/
def IsTruthful {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) : Prop :=
  ∀ d : Fin n → Fin k → ℝ, IsType d → ∀ i : Fin n, ∀ ti ti' : Fin k → ℝ,
    IsAgentType ti → IsAgentType ti' →
      utility alloc pay (Function.update d i ti') i ti ≤
        utility alloc pay (Function.update d i ti) i ti

/-- Strong truthfulness (Def. 5): truthful, and every positive misreport `ti' ≠ ti` is strictly
worse than the truth for some positive declarations of the others; given truthfulness this says
that truth-telling is the only dominant strategy. -/
def IsStronglyTruthful {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) : Prop :=
  IsTruthful alloc pay ∧
    ∀ i : Fin n, ∀ ti ti' : Fin k → ℝ, IsAgentType ti → IsAgentType ti' → ti' ≠ ti →
      ∃ d : Fin n → Fin k → ℝ, IsType d ∧
        utility alloc pay (Function.update d i ti') i ti <
          utility alloc pay (Function.update d i ti) i ti

/-- `c`-approximation (Def. 2): on every positive type vector the chosen allocation has
make-span at most `c` times that of every allocation. -/
def IsApprox {n k : ℕ} [NeZero n] (c : ℝ) (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) :
    Prop :=
  ∀ t : Fin n → Fin k → ℝ, IsType t → ∀ y : Fin k → Fin n,
    makespan t (alloc t) ≤ c * makespan t y

end AlgMechDesign.MinWork


