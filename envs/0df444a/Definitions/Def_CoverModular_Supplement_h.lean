-- Prove2me | Definitions.Def_CoverModular_Supplement_h
-- name    : CoverModular_Supplement_h
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T01:14:46.817772+00:00
-- url     : https://prove2.me/theorems/d8353b03-b152-416e-a99a-a86dd8bd0a16
-- title:
--   LP-based set function $h(\mathcal A)$ of the subset selection problem (17)
-- statement:
--   Consider a linear program with $n$ decision variables indexed by $j$ and $m$ constraints indexed by $i$, with objective coefficients $p\in\mathbb R^n$, constraint matrix $A=[a_{ij}]$ and right-hand side $b\in\mathbb R^m$. Let $\{J_k\}_{k\in\mathcal U}$ be a family of subsets of the variable indices $\{1,\dots,n\}$, indexed by a universe $\mathcal U$, and for $\mathcal A\subseteq\mathcal U$ let $J(\mathcal A)=\{j\mid j\in J_k\text{ for some }k\in\mathcal A\}$. The **LP-based set function** is
--
--   $$
--   h(\mathcal A)=\max_x\ \sum_{1\le j\le n}p_jx_j\quad\text{s.t.}\quad\sum_{1\le j\le n}a_{ij}x_j\le b_i\ (1\le i\le m),\qquad x_j=0\ (j\notin J(\mathcal A)),\qquad x_j\ge0\ (1\le j\le n).
--   $$
--
--   Choosing $\mathcal A$ means choosing which groups of variables may be used. The flexibility design objective of the paper is a special case, and Theorem 2 shows that $h$ is approximately submodular, with a factor given by the column sparsity of $A$.
--
--   **Formalization Note** Constraints and variables are indexed by `Fin m` and `Fin n`. The matrix is natural-number valued (Assumption 1: non-negative integral) and cast to $\mathbb R$. The family $J_k$ is arbitrary: the sets need not be disjoint, nonempty or distinct. Sets $\mathcal A$ are finite subsets of $\mathcal U$. The maximum is the supremum of the objective values over the feasible set. For $b\ge0$ this set contains the value at $x=0$, and when it is bounded above the maximum is attained and equals the supremum. When the LP is unbounded, the paper's $h(\mathcal A)$ is not a real number and the supremum has Lean's junk value $0$. Every theorem that uses $h$ states the boundedness it needs. The module also defines $J(\mathcal A)$ (`jUnion`), the objective $\sum_jp_jx_j$ (`objective`) and feasibility (`Feasible`).
-- source:
--   L. DeValve, S. Pekeč, Y. Wei, Approximate submodularity in network design problems, SSRN 3844987 (author's copy, https://ssrn.com/abstract=3844987), §5.1, display (17), pp.22–23

import Mathlib

namespace CoverModular.Supplement

/-- The index set `J(A) = {j | j ∈ J_k for some k ∈ A}` of the variables admitted by a set `A`
of subset indices (DeValve, Pekeč, Wei, *Approximate submodularity in network design problems*,
SSRN 3844987, §5.1, pp.22–23). -/
def jUnion {U : Type*} [DecidableEq U] {n : ℕ} (J : U → Finset (Fin n)) (A : Finset U) :
    Finset (Fin n) :=
  A.biUnion J

/-- The objective `∑_j p_j x_j` of the LP (17) (SSRN 3844987, §5.1, display (17), p.23). -/
def objective {n : ℕ} (p : Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ j, p j * x j

/-- Feasibility in the LP (17) for the set `A` (SSRN 3844987, §5.1, display (17), p.23):
`∑_j a_ij x_j ≤ b_i` for `1 ≤ i ≤ m`, `x_j = 0` for `j ∉ J(A)`, and `x_j ≥ 0` for all `j`.

**Formalization Note** Constraints are indexed by `Fin m` and variables by `Fin n` (the paper's
`1..m`, `1..n`). The constraint matrix is a natural-number matrix `a : Fin m → Fin n → ℕ`
(Assumption 1: non-negative integral), cast to `ℝ`. -/
def Feasible {U : Type*} [DecidableEq U] {m n : ℕ} (a : Fin m → Fin n → ℕ) (b : Fin m → ℝ)
    (J : U → Finset (Fin n)) (A : Finset U) (x : Fin n → ℝ) : Prop :=
  (∀ i, ∑ j, (a i j : ℝ) * x j ≤ b i) ∧ (∀ j, j ∉ jUnion J A → x j = 0) ∧ ∀ j, 0 ≤ x j

/-- The **LP-based set function** `h` of the subset selection problem (17) (DeValve, Pekeč, Wei,
*Approximate submodularity in network design problems*, SSRN 3844987, §5.1, display (17), p.23):
for a set `A` of subset indices,
`h(A) = max_x ∑_j p_j x_j` s.t. `∑_j a_ij x_j ≤ b_i` (`1 ≤ i ≤ m`), `x_j = 0` (`j ∉ J(A)`),
`x_j ≥ 0` (`1 ≤ j ≤ n`), where `J(A) = ⋃_{k ∈ A} J_k`.

**Formalization Note** The `max` is written as `sSup` of the set of objective values over the
feasible set. Under Assumption 1 (`b ≥ 0`) the set contains the value at `x = 0`; when it is
bounded above the LP attains its supremum and `sSup` is the paper's maximum. When the LP is
unbounded (e.g. a zero column `j ∈ J(A)` with `p_j > 0`) the paper's `h(A)` is not a real number
and `sSup` returns the junk value `0`; every theorem using `h` states the boundedness it needs.
The family `J : U → Finset (Fin n)` is arbitrary (the `J_k` need not be disjoint, nonempty or
distinct) and sets of subset indices are `Finset U`. -/
noncomputable def h {U : Type*} [DecidableEq U] {m n : ℕ} (a : Fin m → Fin n → ℕ)
    (p : Fin n → ℝ) (b : Fin m → ℝ) (J : U → Finset (Fin n)) (A : Finset U) : ℝ :=
  sSup (objective p '' {x | Feasible a b J A x})

end CoverModular.Supplement


