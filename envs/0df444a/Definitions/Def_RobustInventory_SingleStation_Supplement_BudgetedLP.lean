-- Prove2me | Definitions.Def_RobustInventory_SingleStation_Supplement_BudgetedLP
-- name    : RobustInventory_SingleStation_Supplement_BudgetedLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T19:21:24.906275+00:00
-- url     : https://prove2.me/theorems/c7bec67f-1176-4433-9da4-bebfa9c9be3c
-- title:
--   §2.1–§2.2, problems (1) and (2): the linear program with budgeted matrix uncertainty and its linear counterpart
-- statement:
--   This file defines a linear program with budgeted uncertainty in its constraint matrix, and the linear program proposed as its robust counterpart.
--
--   The data are a nominal matrix $\bar A=(\bar a_{ij})\in\mathbb R^{m\times n}$, a set $J$ of index pairs of uncertain coefficients with half-lengths $\hat a_{ij}\ge0$, one budget $\Gamma\ge0$ for the whole set $J$ (not necessarily an integer), and certain vectors $b\in\mathbb R^m$, $c,l,u\in\mathbb R^n$. The uncertainty set is
--   $$\mathcal A=\Big\{A:\ a_{ij}=\bar a_{ij}+\hat a_{ij}z_{ij},\ |z_{ij}|\le1,\ z_{ij}=0\ ((i,j)\notin J),\ \sum_{(i,j)\in J}|z_{ij}|\le\Gamma\Big\}.$$
--
--   1. The **robust problem (1)** minimizes $c'x$ over $l\le x\le u$ such that $Ax\le b$ for every $A\in\mathcal A$.
--   2. The **linear program (2)** minimizes $c'x$ over $(x,q,r,y)$ such that
--   $$\sum_j\bar a_{ij}x_j+q_i\Gamma+\sum_{j:(i,j)\in J}r_{ij}\le b_i\quad\forall i,\qquad q_i+r_{ij}\ge\hat a_{ij}y_j\quad\forall(i,j)\in J,$$
--   $-y\le x\le y$, $l\le x\le u$ and $q,r,y\ge0$.
--
--   For each problem, an optimal point is a feasible point of least objective among all feasible points. These are the two problems related by Theorem 2.1.
--
--   **Formalization Note** The paper writes $|a_{ij}-\bar a_{ij}|/\hat a_{ij}$ in the budget; writing $a_{ij}=\bar a_{ij}+\hat a_{ij}z_{ij}$ avoids the division when $\hat a_{ij}=0$ and gives the same set otherwise. The variables $r_{ij}$ are constrained and used only for $(i,j)\in J$.
-- source:
--   Bertsimas, Thiele, A Robust Optimization Approach to Inventory Theory, Operations Research 54(1):150–168 (2006), pp. 151–152 (PDF 2–3), §2.1, §2.2, problem (1), and Theorem 2.1, problem (2)

import Mathlib

namespace RobustInventory.SingleStation.Supplement

open Matrix

/-- A linear program `minimize c'x subject to A x ≤ b, l ≤ x ≤ u` with `m` rows and `n` columns,
in which only `A` is uncertain (§2.1, pp. 151–152).

* `abar`, `ahat`: the nominal values and the half-lengths of the intervals of the coefficients;
* `J`: the set of indices `(i, j)` of the uncertain coefficients;
* `Γ ≥ 0`: the single budget of uncertainty for all of `J`, not necessarily an integer;
* `b`, `c`, `l`, `u`: the data that are known exactly. -/
structure BudgetedLP (m n : ℕ) where
  abar : Matrix (Fin m) (Fin n) ℝ
  ahat : Matrix (Fin m) (Fin n) ℝ
  J : Finset (Fin m × Fin n)
  Γ : ℝ
  b : Fin m → ℝ
  c : Fin n → ℝ
  l : Fin n → ℝ
  u : Fin n → ℝ
  hahat : ∀ ij ∈ J, 0 ≤ ahat ij.1 ij.2
  hΓ : 0 ≤ Γ

namespace BudgetedLP

variable {m n : ℕ} (P : BudgetedLP m n)

/-- The uncertainty set `𝒜` of §2.2, parametrized by the scaled deviations `z`:
`a_ij = ā_ij + â_ij z_ij` with `z_ij = 0` outside `J`, `|z_ij| ≤ 1` and
`∑_{(i,j) ∈ J} |z_ij| ≤ Γ`. -/
def uncertaintySet : Set (Matrix (Fin m) (Fin n) ℝ) :=
  {A | ∃ z : Fin m → Fin n → ℝ,
    (∀ i j, (i, j) ∉ P.J → z i j = 0) ∧
    (∀ i j, |z i j| ≤ 1) ∧
    ∑ ij ∈ P.J, |z ij.1 ij.2| ≤ P.Γ ∧
    ∀ i j, A i j = P.abar i j + P.ahat i j * z i j}

/-- The objective `c'x`, common to (1) and (2). -/
def cost (x : Fin n → ℝ) : ℝ := ∑ j, P.c j * x j

/-- The bounds `l ≤ x ≤ u`. -/
def InBox (x : Fin n → ℝ) : Prop := ∀ j, P.l j ≤ x j ∧ x j ≤ P.u j

/-- Feasibility in the robust problem (1): `l ≤ x ≤ u` and `A x ≤ b` for every `A ∈ 𝒜`. -/
def RobustFeasible (x : Fin n → ℝ) : Prop :=
  P.InBox x ∧ ∀ A ∈ P.uncertaintySet, ∀ i, (A *ᵥ x) i ≤ P.b i

/-- Feasibility in the linear program (2):
`∑_j ā_ij x_j + q_i Γ + ∑_{j : (i,j) ∈ J} r_ij ≤ b_i` for every row `i`,
`q_i + r_ij ≥ â_ij y_j` and `r_ij ≥ 0` for `(i,j) ∈ J`, `q ≥ 0`, `y ≥ 0`,
`-y ≤ x ≤ y` and `l ≤ x ≤ u`. -/
def CounterpartFeasible (x : Fin n → ℝ) (q : Fin m → ℝ) (r : Fin m → Fin n → ℝ)
    (y : Fin n → ℝ) : Prop :=
  (∀ i, ∑ j, P.abar i j * x j + q i * P.Γ +
      ∑ j ∈ Finset.univ.filter (fun j => (i, j) ∈ P.J), r i j ≤ P.b i) ∧
  (∀ i j, (i, j) ∈ P.J → P.ahat i j * y j ≤ q i + r i j) ∧
  (∀ j, -y j ≤ x j ∧ x j ≤ y j) ∧
  P.InBox x ∧
  (∀ i, 0 ≤ q i) ∧
  (∀ i j, (i, j) ∈ P.J → 0 ≤ r i j) ∧
  (∀ j, 0 ≤ y j)

/-- `x` is optimal for (1). -/
def IsRobustOptimal (x : Fin n → ℝ) : Prop :=
  P.RobustFeasible x ∧ ∀ x', P.RobustFeasible x' → P.cost x ≤ P.cost x'

/-- `(x, q, r, y)` is optimal for (2). -/
def IsCounterpartOptimal (x : Fin n → ℝ) (q : Fin m → ℝ) (r : Fin m → Fin n → ℝ)
    (y : Fin n → ℝ) : Prop :=
  P.CounterpartFeasible x q r y ∧
    ∀ x' q' r' y', P.CounterpartFeasible x' q' r' y' → P.cost x ≤ P.cost x'

end BudgetedLP

end RobustInventory.SingleStation.Supplement


