-- Prove2me | Definitions.Def_CJP83_CoverSeparation_KnapsackRow
-- name    : CJP83_CoverSeparation_KnapsackRow
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T02:26:19.801149+00:00
-- url     : https://prove2.me/theorems/ade637e0-1aba-48dc-9e2c-94cd0456f508
-- title:
--   The knapsack row, minimal covers, configurations, separation, and lifting
-- statement:
--   For a finite index set $K$, let $a_j$ be positive rational coefficients and $a_0$ a rational right-hand side. The single row (2.5) is
--   $$
--   \sum_{j\in K}a_jx_j\le a_0,\qquad x_j\in\{0,1\}.
--   $$
--   A zero–one vector is represented by its support $x\subseteq K$. A **minimal cover** $S$ satisfies $\sum_{j\in S}a_j>a_0$ and $\sum_{j\in S}a_j-a_k\le a_0$ for every $k\in S$, exactly as in (2.6). A **$(1,k)$-configuration** consists of $S^*\subseteq K$, $t\notin S^*$ and $2\le k\le|S^*|$ such that $\sum_{j\in S^*}a_j\le a_0$ and every $Q\subseteq S^*$ of size $k$ makes $Q\cup\{t\}$ a minimal cover (2.8).
--
--   For a point $\bar x\in\mathbb R^K$, the **separation values** are
--   $$
--   \left\{\sum_{j\in s}(1-\bar x_j):s\subseteq K,\ \sum_{j\in s}a_j>a_0\right\},
--   $$
--   the attainable values of (2.12). An intermediate inequality with integer coefficients $f_j$ on $S$ and integer right-hand side $f_0$ is **valid on $S$** when it holds for every feasible zero–one vector supported in $S$. The lifting values are the attainable integer objectives of (2.10), and the relaxed lifting values replace the zero–one condition by $0\le y_j\le1$ on $S$.
--
--   These definitions give a common, literal model for the separation and lifting results. The value sets may be empty; optimal values are subsequently asserted by least or greatest membership, so no default value is assigned to an infeasible problem.
-- source:
--   Crowder, Johnson and Padberg, Solving Large-Scale Zero-One Linear Programming Problems, Operations Research 31 (1983), pp. 810–814, Sections 2.2–2.4, (2.5)–(2.12)

import Mathlib

namespace CJP83.CoverSeparation

/- The zero-one solutions of the single row (2.5), represented by their supports. -/
def IsRowFeasible {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℚ) (a₀ : ℚ) (x : Finset ι) : Prop :=
  (∑ j ∈ x, a j) ≤ a₀

/- The two clauses of (2.6), including its single-deletion formulation. -/
def IsMinimalCover {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℚ) (a₀ : ℚ) (S : Finset ι) : Prop :=
  a₀ < ∑ j ∈ S, a j ∧
    ∀ k ∈ S, (∑ j ∈ S, a j) - a k ≤ a₀

/- The definition (2.8), with the full range 2 ≤ k ≤ |S*|. -/
def IsOneKConfiguration {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℚ) (a₀ : ℚ) (Sstar : Finset ι) (t : ι) (k : ℕ) : Prop :=
  t ∉ Sstar ∧ 2 ≤ k ∧ k ≤ Sstar.card ∧
    (∑ j ∈ Sstar, a j) ≤ a₀ ∧
    ∀ Q : Finset ι, Q ⊆ Sstar → Q.card = k →
      IsMinimalCover a a₀ (insert t Q)

/- The zero-one value at an index, for a support-set representation. -/
def binaryValue {ι : Type*} [DecidableEq ι]
    (x : Finset ι) (j : ι) : ℝ :=
  if j ∈ x then 1 else 0

/- The attainable objective values of the strict-cover problem (2.12). -/
def sepValues {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℚ) (a₀ : ℚ) (xbar : ι → ℝ) : Set ℝ :=
  {v | ∃ s : Finset ι,
    a₀ < ∑ j ∈ s, a j ∧
    v = ∑ j ∈ s, (1 - xbar j)}

/- Validity of an intermediate inequality on solutions supported in S. -/
def IsValidOn {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℚ) (a₀ : ℚ) (S : Finset ι) (f : ι → ℤ) (f₀ : ℤ) : Prop :=
  ∀ x : Finset ι, x ⊆ S → IsRowFeasible a a₀ x →
    (∑ j ∈ x, f j) ≤ f₀

/- Integer objective values attainable in the lifting problem (2.10). -/
def liftValues {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℚ) (a₀ : ℚ) (S : Finset ι) (f : ι → ℤ) (k : ι) : Set ℤ :=
  {v | ∃ x : Finset ι,
    x ⊆ S ∧ (∑ j ∈ x, a j) ≤ a₀ - a k ∧
    v = ∑ j ∈ x, f j}

/- Real objective values attainable in the LP relaxation of (2.10). -/
def relaxedLiftValues {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℚ) (a₀ : ℚ) (S : Finset ι) (f : ι → ℤ) (k : ι) : Set ℝ :=
  {v | ∃ y : ι → ℝ,
    (∀ j, j ∉ S → y j = 0) ∧
    (∀ j ∈ S, 0 ≤ y j ∧ y j ≤ 1) ∧
    (∑ j ∈ S, (a j : ℝ) * y j) ≤ (a₀ - a k : ℚ) ∧
    v = ∑ j ∈ S, (f j : ℝ) * y j}

end CJP83.CoverSeparation


