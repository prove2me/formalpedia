-- Prove2me | Definitions.Def_Timetabling85_ClassTeacher_Problems
-- name    : Timetabling85_ClassTeacher_Problems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:53:35.30426+00:00
-- url     : https://prove2.me/theorems/61fa3ae2-bf5e-458a-b402-2ab7ab732972
-- title:
--   §2.1, pp. 152–153 — the class–teacher problems CT1, CT2, CT3 and the minimum number of days
-- statement:
--   This file fixes the basic class–teacher model of de Werra's *An introduction to timetabling* (§2.1).
--
--   There are $m$ classes $c_1,\dots,c_m$ and $n$ teachers $t_1,\dots,t_n$. The **requirement matrix** $R=(r_{ij})$ is an $m\times n$ matrix of nonnegative integers: $r_{ij}$ is the number of lectures (each one period long) that class $c_i$ must have with teacher $t_j$. Write
--   $$\textstyle r_{i\cdot}=\sum_{j=1}^n r_{ij},\qquad r_{\cdot j}=\sum_{i=1}^m r_{ij}$$
--   for the total load of class $c_i$ and of teacher $t_j$, and for nonnegative integers $s$ and $p$ write $\lfloor s/p\rfloor$ for the largest integer not larger than $s/p$ and $\lceil s/p\rceil$ for the smallest integer not less than $s/p$.
--
--   A schedule over $p$ periods (or days) is an array $x=(x_{ijk})$ of nonnegative integers, $1\le i\le m$, $1\le j\le n$, $1\le k\le p$. Every problem below contains constraint (1): every lecture is scheduled exactly once,
--   $$\sum_{k=1}^p x_{ijk}=r_{ij}\qquad\text{for all } i,j.$$
--
--   1. **CT1** (daily problem, $p$ periods): (1) together with $\sum_j x_{ijk}\le1$ for all $i,k$ (no class has two lectures at once), $\sum_i x_{ijk}\le 1$ for all $j,k$ (no teacher has two lectures at once), and $x_{ijk}\in\{0,1\}$.
--   2. **CT2** (weekly problem, $p$ days), given positive integers $a_i$ and $b_j$, the maximum daily loads of $c_i$ and $t_j$: (1) together with $\sum_j x_{ijk}\le a_i$ for all $i,k$ and $\sum_i x_{ijk}\le b_j$ for all $j,k$.
--   3. **CT3** (balanced weekly problem, $p$ days): (1) together with
--   $$\Big\lfloor \tfrac{r_{i\cdot}}{p}\Big\rfloor\le\sum_{j=1}^n x_{ijk}\le\Big\lceil \tfrac{r_{i\cdot}}{p}\Big\rceil,\qquad \Big\lfloor \tfrac{r_{\cdot j}}{p}\Big\rfloor\le\sum_{i=1}^m x_{ijk}\le\Big\lceil \tfrac{r_{\cdot j}}{p}\Big\rceil,\qquad \Big\lfloor \tfrac{r_{ij}}{p}\Big\rfloor\le x_{ijk}\le\Big\lceil \tfrac{r_{ij}}{p}\Big\rceil$$
--   for all $i,j,k$ (constraints (8), (9), (10)). In (8) and (9) the floor and ceiling are taken of the **total** load divided by $p$.
--
--   Finally, the **minimum number of days** for CT2 is
--   $$p_{\min}=\max\Big(\max_j\Big\lceil \tfrac{r_{\cdot j}}{b_j}\Big\rceil,\ \max_i\Big\lceil \tfrac{r_{i\cdot}}{a_i}\Big\rceil\Big),$$
--   with an empty maximum equal to $0$.
--
--   These are the objects of Propositions 2.1, 2.2 and 2.3 of the paper. In edge-colouring language, $R$ is a bipartite multigraph with $r_{ij}$ parallel edges between $c_i$ and $t_j$, and a schedule assigns one of $p$ colours to each edge.
--
--   **Formalization Note** Classes, teachers and periods are indexed by `Fin m`, `Fin n`, `Fin p`; $R$ and $x$ take values in $\mathbb N$ (constraint (7), "$x_{ijk}\ge0$ integer", is the type). Constraint (4) is written $x_{ijk}\le 1$. The floor and ceiling `lo s p`, `hi s p` are `Nat.floor`/`Nat.ceil` of the rational $s/p$; for $p=0$ Lean returns $0$, and every theorem that needs $p\ge1$ assumes it.
-- source:
--   de Werra, An introduction to timetabling, Eur. J. Oper. Res. 19 (1985), pp. 152–153, §2.1, problems CT1 (1)–(4), CT2 (5)–(7), CT3 (8)–(10), and the minimum-days display on p. 153

import Mathlib

namespace Timetabling85.ClassTeacher

/-- `lo s p = ⌊s / p⌋`, the largest integer not larger than `s / p` (de Werra 1985, p. 153).
The division is in `ℚ`; for `p = 0` Lean's convention gives `s / 0 = 0`. -/
def lo (s p : ℕ) : ℕ := ⌊(s : ℚ) / (p : ℚ)⌋₊

/-- `hi s p = ⌈s / p⌉`, the smallest integer not less than `s / p` (de Werra 1985, p. 153).
The division is in `ℚ`; for `p = 0` Lean's convention gives `s / 0 = 0`. -/
def hi (s p : ℕ) : ℕ := ⌈(s : ℚ) / (p : ℚ)⌉₊

/-- Row sum `∑_{j=1}^n r_ij` of the requirement matrix: all lectures of class `c_i`. -/
def rowSum {m n : ℕ} (R : Fin m → Fin n → ℕ) (i : Fin m) : ℕ := ∑ j, R i j

/-- Column sum `∑_{i=1}^m r_ij` of the requirement matrix: all lectures of teacher `t_j`. -/
def colSum {m n : ℕ} (R : Fin m → Fin n → ℕ) (j : Fin n) : ℕ := ∑ i, R i j

/-- Constraint (1): every lecture is scheduled exactly once,
`∑_{k=1}^p x_ijk = r_ij` for all classes `i` and teachers `j`. -/
def SchedulesAll {m n : ℕ} (R : Fin m → Fin n → ℕ) (p : ℕ)
    (x : Fin m → Fin n → Fin p → ℕ) : Prop :=
  ∀ i j, ∑ k, x i j k = R i j

/-- Problem CT1 (p. 152): constraints (1)–(4). `x i j k` is `1` if class `c_i` and teacher `t_j`
meet at period `k` and `0` otherwise. -/
def IsCT1 {m n : ℕ} (R : Fin m → Fin n → ℕ) (p : ℕ)
    (x : Fin m → Fin n → Fin p → ℕ) : Prop :=
  SchedulesAll R p x ∧
  (∀ i k, ∑ j, x i j k ≤ 1) ∧          -- (2)
  (∀ j k, ∑ i, x i j k ≤ 1) ∧          -- (3)
  (∀ i j k, x i j k ≤ 1)               -- (4): x_ijk ∈ {0, 1}

/-- Problem CT2 (p. 152): constraints (1), (5), (6), (7). `x i j k` is the number of lectures
of class `c_i` with teacher `t_j` assigned to day `k`; (7) (`x_ijk ≥ 0` integer) is the type `ℕ`.
`a i` (resp. `b j`) is the maximum daily number of lectures of class `c_i` (resp. teacher `t_j`). -/
def IsCT2 {m n : ℕ} (R : Fin m → Fin n → ℕ) (p : ℕ) (a : Fin m → ℕ) (b : Fin n → ℕ)
    (x : Fin m → Fin n → Fin p → ℕ) : Prop :=
  SchedulesAll R p x ∧
  (∀ i k, ∑ j, x i j k ≤ a i) ∧        -- (5)
  (∀ j k, ∑ i, x i j k ≤ b j)          -- (6)

/-- Problem CT3 (p. 153): constraints (1), (8), (9), (10). The bounds in (8) and (9) are the
floor and ceiling of the row (resp. column) **total** divided by `p`. -/
def IsCT3 {m n : ℕ} (R : Fin m → Fin n → ℕ) (p : ℕ)
    (x : Fin m → Fin n → Fin p → ℕ) : Prop :=
  SchedulesAll R p x ∧
  (∀ i k, lo (rowSum R i) p ≤ ∑ j, x i j k ∧ ∑ j, x i j k ≤ hi (rowSum R i) p) ∧   -- (8)
  (∀ j k, lo (colSum R j) p ≤ ∑ i, x i j k ∧ ∑ i, x i j k ≤ hi (colSum R j) p) ∧   -- (9)
  (∀ i j k, lo (R i j) p ≤ x i j k ∧ x i j k ≤ hi (R i j) p)                       -- (10)

/-- The minimum number of days of the display on p. 153:
`max (max_j ⌈∑_i r_ij / b_j⌉, max_i ⌈∑_j r_ij / a_i⌉)`; an empty maximum is `0`. -/
def minDays {m n : ℕ} (R : Fin m → Fin n → ℕ) (a : Fin m → ℕ) (b : Fin n → ℕ) : ℕ :=
  max (Finset.univ.sup fun j => hi (colSum R j) (b j))
      (Finset.univ.sup fun i => hi (rowSum R i) (a i))

end Timetabling85.ClassTeacher


