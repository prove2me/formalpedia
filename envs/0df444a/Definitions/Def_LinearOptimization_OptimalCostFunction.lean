-- Prove2me | Definitions.Def_LinearOptimization_OptimalCostFunction
-- name    : LinearOptimization_OptimalCostFunction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-05T21:05:37.430263+00:00
-- url     : https://prove2.me/theorems/1010db1f-43f4-4874-bd50-39d9d3798a28
-- title:
--   Optimal cost as a function of the right-hand side and of the cost vector
-- statement:
--   **(§5.2, p. 212; Eq. (5.2), p. 214; §5.4, pp. 216-217)**
--
--   Standing assumptions of Chapter 5 (p. 202): a standard form problem $\min c'x$ subject to $Ax = b$, $x \ge 0$, where the rows of the $m \times n$ matrix $A$ are linearly independent.
--
--   **Global dependence on $b$** (§5.2, $A$ and $c$ fixed): the feasible set is $P(b) = \{x \mid Ax = b,\ x \ge 0\}$; $S = \{b \mid P(b) \text{ is nonempty}\} = \{Ax \mid x \ge 0\}$, a convex set; and for $b \in S$ the optimal cost function is
--
--   $$F(b) = \min_{x \in P(b)} c'x.$$
--
--   Under the §5.2 standing assumption that the dual feasible set $\{p \mid p'A \le c'\}$ is nonempty, duality implies $F(b)$ is finite for every $b \in S$, and
--
--   $$F(b) = \max_{i=1,\dots,N} (p^i)'b$$
--
--   where $p^1, \dots, p^N$ are the extreme points of the dual feasible set (Eq. (5.2)) — a piecewise linear convex function.
--
--   **Global dependence on $c$** (§5.4, $A$ and $b$ fixed, primal feasible set assumed nonempty): the dual feasible set is $Q(c) = \{p \mid p'A \le c'\}$; $T = \{c \mid Q(c) \text{ is nonempty}\}$; the optimal primal cost $G(c)$ is finite if and only if $c \in T$ (if $c \notin T$ the optimal cost is $-\infty$), and
--
--   $$G(c) = \min_{i=1,\dots,N} c'x^i$$
--
--   over the basic feasible solutions $x^1, \dots, x^N$ of the primal feasible set — a piecewise linear concave function.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, §5.2 pp. 212-214 (S, F, Eq. (5.2)); §5.4 pp. 216-217 (Q, T, G); standing assumptions p. 202

import Definitions.Def_Polyhedron
import Definitions.Def_LinearOptimization_DualLP

/-!
The optimal cost of a standard form problem as a function of the problem
data (global dependence on `b` and on `c`).

Source: Bertsimas & Tsitsiklis, *Introduction to Linear Optimization*,
Athena Scientific 1997, Chapter 5:

- **Standing assumptions (p. 202).** A standard form problem
  `min c'x  s.t.  Ax = b, x ≥ 0`, where the rows of the `m × n` matrix `A`
  are linearly independent. (The rank hypothesis is carried explicitly by
  the theorems, not by these definitions.)
- **§5.2 (pp. 212–214), dependence on `b`** (`A` and `c` fixed): the
  feasible set is `P(b) = {x | Ax = b, x ≥ 0}`; the set
  `S = {b | P(b) ≠ ∅} = {Ax | x ≥ 0}` of feasible right-hand sides is
  convex; for `b ∈ S` the optimal cost function is
  `F(b) = min_{x ∈ P(b)} c'x`. Under the §5.2 standing assumption that the
  dual feasible set `{p | p'A ≤ c'}` is nonempty, duality implies `F(b)` is
  finite for every `b ∈ S`, and `F(b) = max_i (p^i)'b` over the extreme
  points `p^1, …, p^N` of the dual feasible set (Eq. (5.2), p. 214) — a
  piecewise linear convex function. (The Eq. (5.2) representation is a
  consequence recorded for orientation, not minted here.)
- **§5.4 (pp. 216–217), dependence on `c`** (`A` and `b` fixed, primal
  feasible set assumed nonempty): the dual feasible set is
  `Q(c) = {p | p'A ≤ c'}`; `T = {c | Q(c) ≠ ∅}` is the set of cost vectors
  for which the optimal cost `G(c)` is finite (for `c ∉ T` the optimal cost
  is `−∞`, p. 217), and `G(c) = min_i c'x^i` over the basic feasible
  solutions of the primal — a piecewise linear concave function.

Design (see CLAUDE.md): the optimal cost lives in `EReal` via Mission I's
`lpValue` (`⊤` = infeasible, `⊥` = unbounded), so `F` and `G` below are
total `EReal`-valued functions; `T` is phrased as the set of `c` where the
`EReal` value is neither `⊤` nor `⊥` (the book's "optimal cost is finite").
The theorems of this mission introduce real-valued representatives on `S`
resp. `T` via explicit coercion hypotheses, never an ℝ-valued `sInf`.
The dual feasible set `Q(c)` is Mission V's `dualFeasibleStd A c`.
-/

open Matrix

namespace LinearOptimization

/-- **Bertsimas & Tsitsiklis, §5.2 (p. 212).** The set `S = {b | P(b) ≠ ∅}` of right-hand
sides `b` for which the standard form problem `Ax = b, x ≥ 0` is feasible
(a convex set, equal to `{Ax | x ≥ 0}`). -/
def feasibleRhsSet {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    Set (Fin m → ℝ) :=
  {b | (stdPolyhedron A b).Nonempty}

/-- Sanity lemma (Bertsimas & Tsitsiklis, p. 212): `S = {Ax | x ≥ 0}`. -/
theorem feasibleRhsSet_eq_image {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    feasibleRhsSet A = {b | ∃ x : Fin n → ℝ, 0 ≤ x ∧ A.mulVec x = b} := by
  ext b
  constructor
  · rintro ⟨x, hAx, hxnn⟩
    exact ⟨x, hxnn, hAx⟩
  · rintro ⟨x, hxnn, hAx⟩
    exact ⟨x, hAx, hxnn⟩

/-- **Bertsimas & Tsitsiklis, §5.2 (p. 212).** The optimal cost function `F(b)` of the standard
form problem `min c'x, Ax = b, x ≥ 0` as a function of the right-hand side
`b` (`A` and `c` fixed), valued in `EReal` (`⊤` = infeasible, i.e.
`b ∉ S`; `⊥` = unbounded). -/
noncomputable def lpOptimalCostRhs {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) (b : Fin m → ℝ) : EReal :=
  lpValue c (stdPolyhedron A b)

/-- **Bertsimas & Tsitsiklis, §5.4 (p. 216).** The optimal cost function `G(c)` of the standard
form problem `min c'x, Ax = b, x ≥ 0` as a function of the cost vector `c`
(`A` and `b` fixed), valued in `EReal`. -/
noncomputable def lpOptimalCostCost {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) : EReal :=
  lpValue c (stdPolyhedron A b)

/-- **Bertsimas & Tsitsiklis, §5.4 (pp. 216–217).** The set `T` of cost vectors `c` for which
the optimal cost of the (feasible) standard form problem is finite —
neither `⊤` (infeasible) nor `⊥` (unbounded). Under the §5.4 standing
assumption that the primal is feasible, `T = {c | Q(c) ≠ ∅}` where
`Q(c) = {p | p'A ≤ c'}` is the dual feasible set (`dualFeasibleStd A c`). -/
def finiteCostSet {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {c | lpOptimalCostCost A b c ≠ ⊤ ∧ lpOptimalCostCost A b c ≠ ⊥}

end LinearOptimization


