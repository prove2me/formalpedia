-- Prove2me | Definitions.Def_SmaleNinth_KleeMinty
-- name    : SmaleNinth_KleeMinty
-- status  : Definition
-- author  : @ORdos
-- created : 2026-09-06T15:25:10.787193+00:00
-- url     : https://prove2.me/theorems/65a5e86c-442d-4541-a10f-682a163ea9c8
-- title:
--   The Klee–Minty cube and Dantzig's rule
-- statement:
--   The **Klee–Minty cube** is the family of linear programs on which the simplex method with the classical entering rule visits exponentially many vertices. In the presentation used here it is, for each $n \ge 1$,
--
--   $$\text{maximize}\ \sum_{j=1}^{n} 10^{\,n-j} x_j \qquad \text{subject to}\qquad 2\sum_{j=1}^{i-1} 10^{\,i-j} x_j + x_i \;\le\; 100^{\,i-1}\quad (i = 1,\dots,n), \qquad x \ge 0 .$$
--
--   Geometrically the feasible region is a combinatorial $n$-cube whose facets have been sheared by the powers of $10$, so that the objective orders its $2^n$ vertices along a Hamiltonian path.
--
--   **Standard form.** This module records the instance in the equality standard form used by the platform's simplex development, and with $0$-based indices throughout. Variables $0, \dots, n-1$ are the original variables and variables $n, \dots, 2n-1$ are slacks, so the constraint matrix $A$ has $n$ rows and $2n$ columns, with
--
--   $$A_{ij} = \begin{cases} 2\cdot 10^{\,i-j}, & j < i < n,\\ 1, & j = i < n,\\ 0, & i < j < n,\end{cases} \qquad A_{i,\,n+i} = 1,\quad A_{i,\,n+i'} = 0 \ (i' \ne i),$$
--
--   right-hand side $b_i = 100^{\,i}$, and cost vector $c_j = -10^{\,n-1-j}$ on the original variables and $c_j = 0$ on the slacks, the sign turning the maximization into a minimization. The **all-slack basis** selects the $n$ slack columns, $B(i) = n+i$; its associated point sets every original variable to $0$ and every slack to $s_i = 100^{\,i}$, which is the vertex at the origin of the cube.
--
--   **Dantzig's rule.** The platform's notion of a simplex pivot commits to no tie-breaking: it relates a basis-and-point pair to a successor whenever some nonbasic column with negative reduced cost enters and some row attaining the ratio test leaves. **Dantzig's rule** — the largest-coefficient, or most-negative-reduced-cost, rule — is the refinement in which the entering column $j$ additionally satisfies
--
--   $$\bar c_j \;\le\; \bar c_{j'} \quad\text{for every column } j',$$
--
--   where $\bar c_{j'}$ denotes the reduced cost of column $j'$ at the current basis. The minimization ranges over all $2n$ columns rather than only the nonbasic ones; this is equivalent to the usual formulation, since basic columns have reduced cost $0$ while the entering column has negative reduced cost. Ties among minimizers, and among rows attaining the ratio test, remain unconstrained, so the notion covers every implementation of the rule.
-- source:
--   V. Klee, G.J. Minty, How good is the simplex algorithm?, in: Inequalities III (O. Shisha, ed.), Academic Press 1972, pp. 159-175; presentation: V. Chvatal, Linear Programming, Freeman 1983, Chapter 4, problem (4.6); standard form per Bertsimas-Tsitsiklis, Introduction to Linear Optimization, Chapters 1-3.

import Definitions.Def_Polyhedron
import Definitions.Def_LinearOptimization_SimplexPivot

/-!
The Klee–Minty cube in standard form, the all-slack initial basis, and
Dantzig's pivoting rule.

Source: V. Klee, G.J. Minty, *How good is the simplex algorithm?*, in:
Inequalities III (O. Shisha, ed.), Academic Press 1972, pp. 159–175, in the
standard presentation of V. Chvátal, *Linear Programming*, Freeman 1983,
Chapter 4 ("How fast is the simplex method?"), problem (4.6):

    maximize    ∑_{j=1}^{n} 10^{n−j} x_j
    subject to  2 ∑_{j=1}^{i−1} 10^{i−j} x_j + x_i ≤ 100^{i−1}   (i = 1,…,n)
                x_j ≥ 0,

which Dantzig's largest-coefficient entering rule solves in exactly 2ⁿ − 1
simplex iterations from the all-slack starting dictionary.

Here the problem is put in the standard form `min c'x, Ax = b, x ≥ 0` of the
platform's `LinearOptimization` simplex development (Bertsimas–Tsitsiklis
Chapter 3): with 0-based indexing, variables `0, …, n−1` are the original
`x`-variables, variables `n, …, 2n−1` are the slacks, row `i` reads
`2 ∑_{j<i} 10^{i−j} x_j + x_i + s_i = 100^i`, and the objective is
`min −∑_j 10^{n−1−j} x_j`.

`IsDantzigPivot` strengthens the platform's `IsSimplexPivot` (which commits
to no pivoting rule) by requiring the entering index to have the **most
negative** reduced cost — Dantzig's original rule (Bertsimas–Tsitsiklis
§3.4, "largest coefficient" rule; Chvátal Chapter 4). Ties, if any, remain
unconstrained.
-/

open Matrix LinearOptimization

namespace SmaleNinth

/-- The Klee–Minty constraint matrix in standard form (`n` rows, `2n`
columns): row `i` is `2·10^{i−j}` at column `j < i`, `1` at column `i`
(the original variables), and `1` at the slack column `n + i`. -/
def kleeMintyA (n : ℕ) : Matrix (Fin n) (Fin (2 * n)) ℝ :=
  fun i j =>
    if (j : ℕ) < n then
      if (j : ℕ) < (i : ℕ) then 2 * 10 ^ ((i : ℕ) - (j : ℕ))
      else if (j : ℕ) = (i : ℕ) then 1
      else 0
    else if (j : ℕ) = n + (i : ℕ) then 1 else 0

/-- The Klee–Minty right-hand side: `b_i = 100^i` (0-based). -/
def kleeMintyb (n : ℕ) : Fin n → ℝ := fun i => 100 ^ (i : ℕ)

/-- The Klee–Minty cost vector for the minimization form:
`c_j = −10^{n−1−j}` on the original variables, `0` on the slacks. -/
def kleeMintyc (n : ℕ) : Fin (2 * n) → ℝ :=
  fun j => if (j : ℕ) < n then -(10 : ℝ) ^ (n - 1 - (j : ℕ)) else 0

/-- The all-slack starting basis: basic column `i` is the slack column
`n + i`. -/
def kleeMintySlackBasis (n : ℕ) : Fin n ↪ Fin (2 * n) :=
  ⟨fun i => ⟨n + (i : ℕ), by omega⟩, by
    intro a b hab
    have := congrArg (fun x : Fin (2 * n) => (x : ℕ)) hab
    simp only at this
    exact Fin.ext (by omega)⟩

/-- The basic feasible solution of the all-slack basis: every original
variable is `0` and each slack equals its right-hand side `100^i`. -/
def kleeMintySlackSolution (n : ℕ) : Fin (2 * n) → ℝ :=
  fun j => if (j : ℕ) < n then 0 else (100 : ℝ) ^ ((j : ℕ) - n)

/-- **Dantzig's pivoting rule** (largest-coefficient entering rule;
Bertsimas–Tsitsiklis §3.4, Chvátal Chapter 4): a simplex pivot whose
entering index has the most negative reduced cost. The exiting row is
constrained by the ratio test exactly as in `IsSimplexPivot`. -/
def IsDantzigPivot {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (B : Fin m ↪ Fin n) (x : Fin n → ℝ) (B' : Fin m ↪ Fin n)
    (x' : Fin n → ℝ) : Prop :=
  ∃ j ℓ, IsPivotStepAt A c B x B' x' j ℓ ∧
    (∀ i, 0 < pivotColumn A B j i →
      x (B ℓ) / pivotColumn A B j ℓ ≤ x (B i) / pivotColumn A B j i) ∧
    ∀ j' : Fin n, reducedCost A c B j ≤ reducedCost A c B j'

end SmaleNinth


