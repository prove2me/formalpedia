-- Prove2me | Definitions.Def_ManneJobShop_Formulation_Model
-- name    : ManneJobShop_Formulation_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T14:58:23.462902+00:00
-- url     : https://prove2.me/theorems/83aaa1b6-1079-4999-83bb-39ebfbd9bad7
-- title:
--   pp. 219–221: tasks, machines, durations, precedence (5a), delays (5c), delivery dates (6), schedules, make-span, and the integer program (2)–(7)
-- statement:
--   This file fixes the job-shop model of A. S. Manne (1960) and his integer-programming formulation of it.
--
--   **Instance.** There are $n$ tasks. Each task $j$ requires a single machine $\mu(j)\in\{1,\dots,M\}$ for $a_j$ consecutive days, where $a_j$ is an integer (the paper's "integral number of time units"). An integer $T$ is the **horizon**: start days range over $\{0,1,\dots,T\}$. The instance also lists
--
--   1. a set $P$ of **precedence pairs**: $(j,k)\in P$ means that job $j$ precedes job $k$;
--   2. a set $D$ of **exact-delay pairs** with integers $\Theta_{jk}$: $(j,k)\in D$ means that job $k$ starts exactly $\Theta_{jk}$ days after job $j$ is completed;
--   3. optional **delivery dates**: some tasks $j$ carry a day $d_j$ by which they must be completed.
--
--   **Conflicting pairs.** A pair $(j,k)$ with $j<k$ and $\mu(j)=\mu(k)$ is a conflicting pair of machine assignments; $\mathcal C$ denotes the set of these pairs.
--
--   **Schedules.** A vector $x=(x_1,\dots,x_n)$ of integer start days is a **schedule** if
--   $$0\le x_j\le T\ \ (\text{all } j),\qquad x_j-x_k\ge a_k\ \text{ or }\ x_k-x_j\ge a_j\ \ ((j,k)\in\mathcal C),\qquad (1)$$
--   $$x_j+a_j\le x_k\ \ ((j,k)\in P),\quad (5a)\qquad x_j+a_j+\Theta_{jk}=x_k\ \ ((j,k)\in D),\quad (5c)\qquad x_j+a_j\le d_j\ \ (j \text{ with a delivery date}).\quad (6)$$
--   Its **make-span** is the elapsed calendar time for all jobs when the shop starts on day $0$,
--   $$\operatorname{ms}(x)=\max_{1\le j\le n}\,(x_j+a_j)\qquad(n\ge1).$$
--
--   **Manne's integer program.** For integers $x_j$, $y_{jk}$ ($(j,k)\in\mathcal C$) and $t$, the program (2)–(7) requires $0\le x_j\le T$ for all $j$, the conditions (5a), (5c), (6) above,
--   $$0\le y_{jk}\le 1,\quad (2)\qquad (T+a_k)\,y_{jk}+(x_j-x_k)\ge a_k,\quad (3)\qquad (T+a_j)(1-y_{jk})+(x_k-x_j)\ge a_j\quad (4)$$
--   for every $(j,k)\in\mathcal C$, and
--   $$x_j+a_j\le t\qquad (j=1,\dots,n).\qquad (7)$$
--   The value $y_{jk}=1$ means that job $j$ precedes job $k$, and $y_{jk}=0$ that $k$ precedes $j$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Tasks are `Fin n` (task $j$ of the paper is index $j-1$) and machines `Fin M`. Durations, start days, the horizon, delays, delivery dates, $y$ and $t$ are integers (`ℤ`), so differences and $1-y_{jk}$ are not truncated; nonnegativity of $x$ is stated explicitly. The paper's footnote calls $T$ a "redundant upper bound upon the unknowns $x_j$"; the formalization makes it explicit by requiring $0\le x_j\le T$ on both the schedule side and the integer-program side, and does not assume redundancy. Durations are not required to be positive. The variable $y$ is a function on all pairs but only its values on conflicting pairs are constrained. The paper writes (6) for "the last task which the shop is to perform upon the item"; here a delivery date may be attached to any task (`due j = some d`), which contains the paper's case. (5b) is (5a) for two pairs and needs no separate field. The make-span uses `Finset.sup'` and therefore needs `[NeZero n]`.
-- source:
--   Manne, On the Job-Shop Scheduling Problem, Operations Research 8 (1960), pp. 219–221, conditions (1)–(7); p. 222, "m possible conflicting pairs of machine assignments"

import Mathlib

namespace ManneJobShop.Formulation

/-- A job-shop instance in the sense of Manne (1960), pp. 219–221. There are `n` tasks, indexed
`0, …, n-1` (the paper's task `j` is index `j - 1`). Task `j` needs the single machine `mach j` for
`a j` consecutive days. `T` is the horizon: start days range over `0, 1, …, T` (p. 219).
`(j, k) ∈ prec` imposes (5a) `x_j + a_j ≤ x_k`; `(j, k) ∈ delay` imposes (5c)
`x_j + a_j + Θ_jk = x_k`; `due j = some d` imposes the delivery date (6) `x_j + a_j ≤ d`. -/
structure Instance (n : ℕ) where
  /-- number of machines -/
  M : ℕ
  /-- the single machine each task requires -/
  mach : Fin n → Fin M
  /-- durations `a_j` (integral numbers of days) -/
  a : Fin n → ℤ
  /-- the horizon `T`: start days lie in `{0, …, T}` -/
  T : ℤ
  /-- precedence pairs for (5a): `(j, k) ∈ prec` means job `j` precedes job `k` -/
  prec : Finset (Fin n × Fin n)
  /-- pairs carrying an exact delay, condition (5c) -/
  delay : Finset (Fin n × Fin n)
  /-- the exact delays `Θ_jk` of (5c), read on `delay` only -/
  Θ : Fin n → Fin n → ℤ
  /-- delivery dates `d_j` of (6), where present -/
  due : Fin n → Option ℤ

variable {n : ℕ}

/-- The conflicting pairs of machine assignments (p. 222): pairs `(j, k)` with `j < k` whose tasks
use the same machine. Each carries one 0–1 variable `y_jk`. -/
def conflicts (I : Instance n) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ I.mach p.1 = I.mach p.2)

/-- A schedule: integer start days `x_j ∈ {0, …, T}` (p. 219) satisfying the noninterference
condition (1) on every conflicting pair, precedence (5a), exact delays (5c) and delivery
dates (6). -/
def IsSchedule (I : Instance n) (x : Fin n → ℤ) : Prop :=
  (∀ j, 0 ≤ x j ∧ x j ≤ I.T) ∧
  (∀ p ∈ conflicts I, x p.1 - x p.2 ≥ I.a p.2 ∨ x p.2 - x p.1 ≥ I.a p.1) ∧
  (∀ p ∈ I.prec, x p.1 + I.a p.1 ≤ x p.2) ∧
  (∀ p ∈ I.delay, x p.1 + I.a p.1 + I.Θ p.1 p.2 = x p.2) ∧
  (∀ j d, I.due j = some d → x j + I.a j ≤ d)

/-- The make-span of a schedule, `max_j (x_j + a_j)`: the elapsed calendar time for the
performance of all jobs when the shop starts on day 0 (p. 219). Needs at least one task. -/
def makespan [NeZero n] (I : Instance n) (x : Fin n → ℤ) : ℤ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j => x j + I.a j)

/-- Manne's integer program (2)–(7), p. 221: integer start days `0 ≤ x_j ≤ T`, integer `y_jk` on
every conflicting pair with (2) `0 ≤ y_jk ≤ 1`, (3) `(T + a_k) y_jk + (x_j - x_k) ≥ a_k`,
(4) `(T + a_j)(1 - y_jk) + (x_k - x_j) ≥ a_j`, together with (5a), (5c), (6) and
(7) `x_j + a_j ≤ t` for every task. `y` is read on conflicting pairs only. -/
def IsIPFeasible (I : Instance n) (x : Fin n → ℤ) (y : Fin n → Fin n → ℤ) (t : ℤ) : Prop :=
  (∀ j, 0 ≤ x j ∧ x j ≤ I.T) ∧
  (∀ p ∈ conflicts I,
    (0 ≤ y p.1 p.2 ∧ y p.1 p.2 ≤ 1) ∧
    (I.T + I.a p.2) * y p.1 p.2 + (x p.1 - x p.2) ≥ I.a p.2 ∧
    (I.T + I.a p.1) * (1 - y p.1 p.2) + (x p.2 - x p.1) ≥ I.a p.1) ∧
  (∀ p ∈ I.prec, x p.1 + I.a p.1 ≤ x p.2) ∧
  (∀ p ∈ I.delay, x p.1 + I.a p.1 + I.Θ p.1 p.2 = x p.2) ∧
  (∀ j d, I.due j = some d → x j + I.a j ≤ d) ∧
  (∀ j, x j + I.a j ≤ t)

end ManneJobShop.Formulation


