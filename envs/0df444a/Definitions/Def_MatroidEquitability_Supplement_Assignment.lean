-- Prove2me | Definitions.Def_MatroidEquitability_Supplement_Assignment
-- name    : MatroidEquitability_Supplement_Assignment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:25:53.409539+00:00
-- url     : https://prove2.me/theorems/7d028120-efb6-490f-b66e-18126476f162
-- title:
--   Fractional and integral assignments as matrices, and the prefix discrepancy $D(i,t)$
-- statement:
--   Rows $i\in[m]$ are machines and columns $j\in[n]$ are jobs.
--
--   1. A **fractional assignment** is a matrix $x\in[0,1]^{m\times n}$ in which every column sums to $1$. The bipartite graph is the support of $x$: $(i,j)$ is an edge exactly when $x_{ij}\neq0$.
--   2. An **assignment** is a matrix $y\in\{0,1\}^{m\times n}$ in which every column sums to $1$, so every job goes to a single machine, and $y_{ij}=0$ whenever $x_{ij}=0$, so every job goes to an adjacent machine.
--   3. For job weights $d\in\mathbb R^n$, the **prefix discrepancy** of row $i$ at $t$ is
--   $$D(i,t)=\sum_{j=1}^t d_jy_{ij}-\sum_{j=1}^t d_jx_{ij}.$$
--
--   These are the objects of the weighted carpool conjecture (Conjecture 3), disproved by Theorem 19.
--
--   **Formalization Note** Matrices are functions `Fin m → Fin n → ℝ`. The paper's column $j$ is the element of `Fin n` of value $j-1$, so the prefix $\{1,\dots,t\}$ is the set of columns of value below $t$.
-- source:
--   Bérczi, Liu, Reis, Tarnawski, Weighted Equitability and Matroid-Constrained Discrepancy, arXiv:2608.13983 (held version sha256 0675891a…), assignments p.3 (PDF p.5); matrix convention before Theorem 19, p.21 (PDF p.23); D(r,t), p.22 (PDF p.24)

import Mathlib

namespace MatroidEquitability

namespace Supplement

/-- A fractional assignment given as a matrix (§7, printed p.21 = PDF p.23 of Bérczi, Liu, Reis,
Tarnawski, *Weighted Equitability and Matroid-Constrained Discrepancy*, arXiv:2608.13983 (held version
sha256 0675891a…); definition on p.3): `x ∈ [0, 1]^{m×n}` with every column sum equal to `1`. Rows are
machines, columns are jobs; the bipartite graph is the support of `x`. -/
def IsFractionalAssignment {m n : ℕ} (x : Fin m → Fin n → ℝ) : Prop :=
  (∀ i j, 0 ≤ x i j ∧ x i j ≤ 1) ∧ ∀ j, ∑ i, x i j = 1

/-- An (integral) assignment `y ∈ {0, 1}^{m×n}` for the bipartite graph given by the support of `x`
(p.3 and p.21): every column `j` (job) is assigned to exactly one row (machine), and `y_ij = 0` whenever
`x_ij = 0`. -/
def IsAssignment {m n : ℕ} (x y : Fin m → Fin n → ℝ) : Prop :=
  (∀ i j, y i j = 0 ∨ y i j = 1) ∧ (∀ j, ∑ i, y i j = 1) ∧ ∀ i j, x i j = 0 → y i j = 0

/-- The prefix discrepancy of row `i` at prefix length `t` (p.22):
`D(i, t) = Σ_{j=1}^t d_j y_ij − Σ_{j=1}^t d_j x_ij`, columns taken in the order of `Fin n`.

**Formalization Note.** The paper's column `j ∈ [n]` is the element of `Fin n` of value `j − 1`, so the
prefix `{1, …, t}` is `{j : j.val < t}`. -/
def prefixDisc {m n : ℕ} (d : Fin n → ℝ) (x y : Fin m → Fin n → ℝ) (i : Fin m) (t : ℕ) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < t), d j * y i j -
    ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < t), d j * x i j

end Supplement

end MatroidEquitability


