-- Prove2me | Definitions.Def_UnitSquarePack_NPHard_TesterSystem
-- name    : UnitSquarePack_NPHard_TesterSystem
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T18:18:19.535515+00:00
-- url     : https://prove2.me/theorems/bff4d90e-fed3-4f24-8fa1-9d7131302e44
-- title:
--   The tester inequalities (3)–(6) of the clause components
-- statement:
--   For $n$ clause components $i = 0, \dots, n-1$ (clause $i$ at the $i$-th position from the top) let
--   $$t_i = 3(i+1) + \tfrac12 i(i+1), \qquad t_{-1} = 0,$$
--   the number of tester columns in the components $0, \dots, i$. Clause $i$ has the literal rows $\ell_{3i}, \ell_{3i+1}, \ell_{3i+2}$, the tester rows $r_{i,0}, \dots, r_{i,2t_i}$ and the tester columns $c_{i,0}, \dots, c_{i,2+i}$. The variables are $y_p$ ($0 \le p < 3n$), equal to $1$ when the $p$-th SWITCH gadget creates a vertical stack, and the crossing values $x(a, c_{p,q})$ for each row $a$ of clause $i$ and each tester column $c_{p,q}$ with $p \le i$. The **tester inequalities** are:
--   $$\text{(3)}\quad 2\sum_{p=0}^{3i+2} y_p + \sum_{p=0}^{i}\sum_{q=0}^{3+p-1} x(r_{i,j}, c_{p,q}) \le 2(i+1+t_i) \qquad (0 \le i < n,\ 0 \le j < 1+2t_i),$$
--   $$\text{(4)}\quad (1-y_{3i})\Big(2\sum_{p=0}^{3i-1} y_p + \sum_{p=0}^{i}\sum_{q=0}^{3+p-1} x(\ell_{3i}, c_{p,q})\Big) \le 2(i + t_{i-1}) \qquad (0 \le i < n),$$
--   $$\text{(5)}\quad (1-y_{3i+m})\Big(2\sum_{p=0}^{3i+m-1} y_p + \sum_{p=0}^{i}\sum_{q=0}^{3+p-1} x(\ell_{3i+m}, c_{p,q})\Big) \le 2(1 + i + t_{i-1}) \qquad (0 \le i < n,\ m \in \{1,2\}),$$
--   $$\text{(6)}\quad \sum_{i=p}^{n-1}\sum_{m=0}^{2} (1-y_{3i+m})\big(2 - x(\ell_{3i+m}, c_{p,q})\big) + \sum_{i=p}^{n-1}\sum_{j=0}^{2t_i}\big(2 - x(r_{i,j}, c_{p,q})\big) \le 4 \qquad (0 \le p < n,\ 0 \le q < 3+p).$$
--
--   **Formalization Note.** `y p` is $y_p$, `xr i j p q` is $x(r_{i,j}, c_{p,q})$ and `xl r p q` is $x(\ell_r, c_{p,q})$, all integer valued; values outside the index ranges above are never used. `testerCount i` is $t_i$ and `testerCountPrev i` is $t_{i-1}$ (with $t_{-1} = 0$). The range of $q$ in (6) is $0 \le q < 3 + p$; the paper prints $3 + i$ with $i$ unbound, while clause $p$ has exactly $3 + p$ tester columns (p. 44).
-- source:
--   Abrahamsen and Stade, Hardness of Packing, Covering and Partitioning Simple Polygons with Unit Squares, arXiv:2404.09835v2, p. 48, §4.8, Eqs. (3)–(6) (pp. 48, 50)

import Mathlib

set_option autoImplicit false

namespace UnitSquarePack.NPHard

open Finset

/-- `t_i = 3(i + 1) + i(i + 1)/2`, the number of tester columns in the clause components
`0, …, i` (p. 44). The product `i(i + 1)` is even, so the division is exact. -/
def testerCount (i : ℕ) : ℕ := 3 * (i + 1) + i * (i + 1) / 2

/-- `t_{i-1}`, with `t_{-1} = 0` (the value of the formula at `i = -1`). -/
def testerCountPrev (i : ℕ) : ℕ := if i = 0 then 0 else testerCount (i - 1)

/-- The inequalities (3)–(6) of §4.8 for `n` clauses. `y p` is the SWITCH variable `y_p`;
`xr i j p q` is `x(r_{i,j}, c_{p,q})`, the growth of the tester row `r_{i,j}` at the tester column
`c_{p,q}`; `xl r p q` is `x(ℓ_r, c_{p,q})`, the growth of the literal row `ℓ_r` at `c_{p,q}`.
Clause `i` has the tester columns `c_{i,0}, …, c_{i,2+i}`, the tester rows
`r_{i,0}, …, r_{i,2t_i}` and the literal rows `ℓ_{3i}, ℓ_{3i+1}, ℓ_{3i+2}`.
In (6) the tester columns are `0 ≤ q < 3 + p` (the paper prints `3 + i`). -/
def TesterInequalities (n : ℕ) (y : ℕ → ℤ) (xr : ℕ → ℕ → ℕ → ℕ → ℤ) (xl : ℕ → ℕ → ℕ → ℤ) :
    Prop :=
  -- (3): for `0 ≤ i < n`, `0 ≤ j < 1 + 2t_i`
  (∀ i < n, ∀ j < 1 + 2 * testerCount i,
    2 * ∑ p ∈ range (3 * i + 3), y p +
      ∑ p ∈ range (i + 1), ∑ q ∈ range (3 + p), xr i j p q
      ≤ 2 * ((i : ℤ) + 1 + testerCount i)) ∧
  -- (4): for `0 ≤ i < n`
  (∀ i < n,
    (1 - y (3 * i)) *
        (2 * ∑ p ∈ range (3 * i), y p +
          ∑ p ∈ range (i + 1), ∑ q ∈ range (3 + p), xl (3 * i) p q)
      ≤ 2 * ((i : ℤ) + testerCountPrev i)) ∧
  -- (5): for `0 ≤ i < n` and `m ∈ {1, 2}`
  (∀ i < n, ∀ m ∈ ({1, 2} : Finset ℕ),
    (1 - y (3 * i + m)) *
        (2 * ∑ p ∈ range (3 * i + m), y p +
          ∑ p ∈ range (i + 1), ∑ q ∈ range (3 + p), xl (3 * i + m) p q)
      ≤ 2 * (1 + (i : ℤ) + testerCountPrev i)) ∧
  -- (6): for `0 ≤ p < n` and `0 ≤ q < 3 + p`
  (∀ p < n, ∀ q < 3 + p,
    ∑ i ∈ Ico p n, ∑ m ∈ range 3, (1 - y (3 * i + m)) * (2 - xl (3 * i + m) p q) +
      ∑ i ∈ Ico p n, ∑ j ∈ range (2 * testerCount i + 1), (2 - xr i j p q)
      ≤ 4)

end UnitSquarePack.NPHard


