-- Prove2me | Definitions.Def_LinearOptimization_SimplexPivot
-- name    : LinearOptimization_SimplexPivot
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-05T17:22:57.105721+00:00
-- url     : https://prove2.me/theorems/26eca352-fab2-4dc8-952e-7c08c91cc4e9
-- title:
--   Simplex method iteration (pivot) and the lexicographic pivoting rule
-- statement:
--   **(An iteration of the simplex method, §3.2 pp. 90–91, as a predicate)** A typical iteration (pivot) starting from a basis of basic columns $A_{B(1)}, \dots, A_{B(m)}$ and an associated basic feasible solution $x$:
--
--   1. Compute the reduced costs $\bar{c}_j = c_j - c_B'B^{-1}A_j$ for all nonbasic indices $j$; if they are all nonnegative, the current basic feasible solution is optimal and the algorithm terminates; else choose some $j$ for which $\bar{c}_j < 0$.
--   2. Compute $u = B^{-1}A_j$; if no component of $u$ is positive, $\theta^* = \infty$, the optimal cost is $-\infty$, and the algorithm terminates.
--   3. If some component of $u$ is positive, let $\theta^* = \min_{\{i : u_i > 0\}} x_{B(i)}/u_i$.
--   4. Let $\ell$ be such that $\theta^* = x_{B(\ell)}/u_\ell$; form a new basis by replacing $A_{B(\ell)}$ with $A_j$; the new basic feasible solution $y$ has $y_j = \theta^*$ and $y_{B(i)} = x_{B(i)} - \theta^* u_i$ for $i \ne \ell$.
--
--   Encoded as the predicate IsSimplexPivot relating $(B, x)$ to the successor $(\bar{B}, y)$, with terminal predicates for the two stopping criteria.
--
--   Sub-predicate for the lexicographic pivoting rule: **(Definition 3.5)** a vector $u \in \mathbb{R}^n$ is *lexicographically larger* (or *smaller*) than $v \in \mathbb{R}^n$ if $u \ne v$ and the first nonzero component of $u - v$ is positive (or negative, respectively), written $u \stackrel{L}{>} v$ or $u \stackrel{L}{<} v$;
--
--   **(lexicographic pivoting rule, p. 109)**
--
--   1. choose an entering column $A_j$ arbitrarily, as long as its reduced cost $\bar{c}_j$ is negative, and let $u = B^{-1}A_j$;
--   2. for each $i$ with $u_i > 0$, divide the $i$th row of the tableau (including the entry in the zeroth column) by $u_i$ and choose the lexicographically smallest row; if row $\ell$ is lexicographically smallest, the $\ell$th basic variable $x_{B(\ell)}$ exits the basis.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, §3.2 iteration box, pp. 90-91; Definition 3.5, p. 108; lexicographic pivoting rule box, p. 109

import Definitions.Def_Polyhedron
import Definitions.Def_LinearOptimization_ReducedCost
import Definitions.Def_LinearOptimization_FeasibleDirection

/-!
The simplex pivot as a predicate, terminal states, the lexicographic order,
the simplex tableau, and the lexicographic pivoting rule.

Source: Bertsimas & Tsitsiklis, *Introduction to Linear Optimization*,
Athena Scientific 1997:

- **"An iteration of the simplex method" box (§3.2, pp. 90–91).** A typical
  iteration starts with a basis of basic columns `A_{B(1)}, …, A_{B(m)}` and
  an associated basic feasible solution `x`:
  1. compute the reduced costs `c̄_j`; if all are nonnegative, `x` is
     optimal and the algorithm terminates; else pick `j` with `c̄_j < 0`;
  2. compute `u = B⁻¹A_j`; if no component of `u` is positive,
     `θ* = ∞`, the optimal cost is `−∞`, and the algorithm terminates;
  3. else let `θ* = min_{i : u_i > 0} x_{B(i)}/u_i`;
  4. let `ℓ` attain the minimum; the new basis replaces `A_{B(ℓ)}` by
     `A_j`, and the new basic feasible solution is `y = x + θ*d` with `d`
     the `j`th basic direction.
- **Definition 3.5 (p. 108).** `u ∈ ℝᵏ` is *lexicographically larger* than
  `v` (`u >ᴸ v`) if `u ≠ v` and the first nonzero component of `u − v` is
  positive.
- **Lexicographic pivoting rule box (p. 109).** Choose any entering column
  `A_j` with `c̄_j < 0` and let `u = B⁻¹A_j`; for each `i` with `u_i > 0`,
  divide the `i`th row of the tableau (including the zeroth-column entry)
  by `u_i` and choose the lexicographically smallest row; if row `ℓ` is
  lexicographically smallest, `x_{B(ℓ)}` exits the basis. (The book notes
  the lexicographically smallest row is unique, since two proportional rows
  of `B⁻¹A` would contradict `rank(A) = m`.)
- **Tableau (§3.3 / §3.4, pp. 98–99, 109–110).** For `i = 1, …, m` the
  `i`th tableau row is `[(B⁻¹b)_i | (B⁻¹A)_i]`; the zeroth row is
  `[−c_B'B⁻¹b | c' − c_B'B⁻¹A]`.

Design (algorithms are predicates, not programs — see CLAUDE.md): a pivot
relates a basis/BFS pair `(B, x)` to a successor `(B', x')`; no tie-breaking
is committed, so every theorem quantifies over every pivoting rule; the
lexicographic rule is a strengthening of the exit choice. `B⁻¹` is Lean's
`Matrix.inv`, guarded by `IsStdBasis A B` in every admissible state.
-/

open Matrix

namespace LinearOptimization

/-- The vector `u = B⁻¹A_j` computed in Step 2 of the simplex iteration
(Bertsimas & Tsitsiklis, p. 90); its entries are the negatives of the basic components of the
`j`th basic direction. -/
noncomputable def pivotColumn {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (B : Fin m ↪ Fin n) (j : Fin n) : Fin m → ℝ :=
  (basisMatrix A B)⁻¹.mulVec (fun i => A i j)

/-- An admissible state of the simplex method on `min c'x, Ax = b, x ≥ 0`
(Bertsimas & Tsitsiklis, pp. 90–91): a genuine basis `B` together with its associated basic
feasible solution `x` (feasible, and all nonbasic components zero). -/
def IsSimplexState {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (B : Fin m ↪ Fin n) (x : Fin n → ℝ) : Prop :=
  IsStdBasis A B ∧ x ∈ stdPolyhedron A b ∧ ∀ j ∉ Set.range B, x j = 0

/-- The core of one simplex pivot with entering index `j` and exiting row
`ℓ` (Bertsimas & Tsitsiklis, Steps 1–4, pp. 90–91, and Eqs. (3.2)–(3.4), pp. 88–89): `j` is
nonbasic with negative reduced cost, `u_ℓ > 0`, the new basis `B'` replaces
`B(ℓ)` by `j`, and the new point is `x' = x + θ* d` with `θ* = x_{B(ℓ)}/u_ℓ`
and `d` the `j`th basic direction. (The choice of `ℓ` among the rows with
`u_i > 0` is constrained by the pivoting rule — see `IsSimplexPivot` and
`IsLexicographicPivot`.) -/
def IsPivotStepAt {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (B : Fin m ↪ Fin n) (x : Fin n → ℝ) (B' : Fin m ↪ Fin n) (x' : Fin n → ℝ)
    (j : Fin n) (ℓ : Fin m) : Prop :=
  j ∉ Set.range B ∧
  reducedCost A c B j < 0 ∧
  0 < pivotColumn A B j ℓ ∧
  (∀ i, i ≠ ℓ → B' i = B i) ∧
  B' ℓ = j ∧
  x' = x + (x (B ℓ) / pivotColumn A B j ℓ) • basicDirection A B j

/-- **Bertsimas & Tsitsiklis, "An iteration of the simplex method" (pp. 90–91), as a
predicate.** `(B, x)` pivots to `(B', x')`: some entering index `j` with
`c̄_j < 0` and some exiting row `ℓ` attaining the ratio test
`θ* = min_{i : u_i > 0} x_{B(i)}/u_i`. No tie-breaking is committed, so
this predicate covers every pivoting rule. -/
def IsSimplexPivot {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (B : Fin m ↪ Fin n) (x : Fin n → ℝ) (B' : Fin m ↪ Fin n) (x' : Fin n → ℝ) :
    Prop :=
  ∃ j ℓ, IsPivotStepAt A c B x B' x' j ℓ ∧
    ∀ i, 0 < pivotColumn A B j i →
      x (B ℓ) / pivotColumn A B j ℓ ≤ x (B i) / pivotColumn A B j i

/-- Terminal state of Step 1 (Bertsimas & Tsitsiklis, p. 90): all reduced costs of nonbasic
variables are nonnegative, so the current basic feasible solution is
optimal and the algorithm terminates. -/
def IsSimplexOptimalTerminal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) (B : Fin m ↪ Fin n) : Prop :=
  ∀ j ∉ Set.range B, 0 ≤ reducedCost A c B j

/-- Terminal state of Step 2 (Bertsimas & Tsitsiklis, p. 90): some entering index `j` has
`c̄_j < 0` but no component of `u = B⁻¹A_j` is positive, so `θ* = ∞`, the
optimal cost is `−∞`, and the algorithm terminates. -/
def IsSimplexUnboundedTerminal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) (B : Fin m ↪ Fin n) : Prop :=
  ∃ j ∉ Set.range B, reducedCost A c B j < 0 ∧ ∀ i, pivotColumn A B j i ≤ 0

/-- **Bertsimas & Tsitsiklis, Definition 3.5 (p. 108).** The lexicographic order on `Fin k → ℝ`:
`LexLt u v` means `v` is lexicographically larger than `u` (`v >ᴸ u`), i.e.
`u ≠ v` and the first nonzero component of `v − u` is positive — rendered
as: at some index `i`, `u i < v i` while `u` and `v` agree at every earlier
index. -/
def LexLt {k : ℕ} (u v : Fin k → ℝ) : Prop :=
  ∃ i, u i < v i ∧ ∀ i', i' < i → u i' = v i'

/-- `v` is lexicographically positive: `v >ᴸ 0` (Bertsimas & Tsitsiklis, §3.4, p. 108). -/
def LexPos {k : ℕ} (v : Fin k → ℝ) : Prop :=
  LexLt 0 v

/-- The `i`th row (`i = 1, …, m` in the book's numbering) of the simplex
tableau at the basis `B` (Bertsimas & Tsitsiklis, §3.3 pp. 98–99, §3.4 p. 110): the zeroth
column carries `(B⁻¹b)_i`, and the remaining `n` entries are the `i`th row
of `B⁻¹A`. -/
noncomputable def tableauRow {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (B : Fin m ↪ Fin n) (i : Fin m) : Fin (n + 1) → ℝ :=
  Fin.cons ((basisMatrix A B)⁻¹.mulVec b i) (fun j => ((basisMatrix A B)⁻¹ * A) i j)

/-- The zeroth row of the simplex tableau at the basis `B` (Bertsimas & Tsitsiklis, §3.3
pp. 98–99): `[−c_B'B⁻¹b | c' − c_B'B⁻¹A]` — the negative of the current
cost followed by the row vector of reduced costs. -/
noncomputable def tableauZerothRow {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (B : Fin m ↪ Fin n) : Fin (n + 1) → ℝ :=
  Fin.cons (-((fun i => c (B i)) ⬝ᵥ (basisMatrix A B)⁻¹.mulVec b))
    (fun j => reducedCost A c B j)

/-- **Bertsimas & Tsitsiklis, lexicographic pivoting rule (p. 109), as a predicate.** A pivot
whose exit choice follows the lexicographic rule: the entering column `j`
is arbitrary subject to `c̄_j < 0`, and among the rows `i` with `u_i > 0`
the exiting row `ℓ` is the one whose tableau row divided by `u_i`
(zeroth-column entry included) is lexicographically smallest — strictly
smallest against every other candidate row, per the book's uniqueness
remark. (The zeroth-column comparison entry `(B⁻¹b)_ℓ/u_ℓ` is the ratio
`x_{B(ℓ)}/u_ℓ`, so the lexicographic rule refines the ratio test whenever
the tableau rows are lexicographically positive.) -/
def IsLexicographicPivot {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ)
    (B : Fin m ↪ Fin n) (x : Fin n → ℝ) (B' : Fin m ↪ Fin n) (x' : Fin n → ℝ) :
    Prop :=
  ∃ j ℓ, IsPivotStepAt A c B x B' x' j ℓ ∧
    ∀ i, 0 < pivotColumn A B j i → i ≠ ℓ →
      LexLt ((pivotColumn A B j ℓ)⁻¹ • tableauRow A b B ℓ)
        ((pivotColumn A B j i)⁻¹ • tableauRow A b B i)

end LinearOptimization


