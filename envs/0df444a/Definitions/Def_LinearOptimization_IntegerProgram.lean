-- Prove2me | Definitions.Def_LinearOptimization_IntegerProgram
-- name    : LinearOptimization_IntegerProgram
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-09T15:58:52.279504+00:00
-- url     : https://prove2.me/theorems/e6d4f3ca-531d-4f63-a10a-9b2321a8815e
-- title:
--   Mixed integer programming problem
-- statement:
--   **(The mixed integer programming problem — Bertsimas & Tsitsiklis, Ch 10, p. 452.)** Given matrices $A$, $B$, and vectors $b$, $c$, $d$, the problem
--
--   $$\begin{aligned}\text{minimize}\quad & c'x + d'y\\ \text{subject to}\quad & Ax + By = b\\ & x, y \ge 0\\ & x\ \text{integer},\end{aligned}$$
--
--   is the *mixed integer programming problem*. (Even if there are inequality constraints, the problem can be written in the above form by adding slack or surplus variables.)
--
--   If there are no continuous variables $y$, the problem is called the *integer programming problem*; if furthermore the components of $x$ are restricted to be either $0$ or $1$, it is the *zero-one (or binary) integer programming problem*. It is customary to assume that the entries of $A$, $B$, $b$, $c$, $d$ are integers.
--
--   Also covers the inequality-form integer program of Section 11.4, problem (11.5):
--
--   $$Z_{IP} = \min\{c'x : Ax \ge b,\ Dx \ge d,\ x\ \text{integer}\}$$
--
--   with $A$, $D$, $b$, $c$, $d$ of integer entries, whose optimal cost $Z_{IP}$ is EReal-valued.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Ch 10 opening, p. 452 (mixed integer programming problem); inequality form: Bertsimas & Tsitsiklis, Section 11.4, problem (11.5), p. 494

import Definitions.Def_Polyhedron

/-!
Integer and mixed integer programming problems.

Source: Bertsimas & Tsitsiklis, *Introduction to Linear Optimization*,
Athena Scientific 1997:

- **The mixed integer programming problem (Ch. 10 opening, p. 452).**
  `min c'x + d'y` subject to `Ax + By = b`, `x, y ≥ 0`, `x` integer.
  If there are no continuous variables `y`, it is the *integer programming
  problem*; if furthermore the components of `x` are restricted to `0` or
  `1`, it is the *zero-one (binary) integer programming problem*. It is
  customary to assume the data entries are integers (theorems take
  `ℤ`-valued data coerced to `ℝ`, series guard 11).
- **The §11.4 inequality form, problem (11.5) (p. 494).**
  `Z_IP = min {c'x | Ax ≥ b, Dx ≥ d, x integer}`, with all data integer.

Encoding (mission design note): integrality of a mixed vector is
`∀ i ∈ I, ∃ z : ℤ, x i = z` over the designated index set `I` of integer
variables — so the p. 452 block problem `(x, y)` is carried by a single
variable vector with `I` = the `x`-block indices (inequality constraints
reduce to this form by slack/surplus variables, as the book notes), and
the pure-integer case is `I = univ`. All optimal costs live in `EReal`
via Mission I's `lpValue` (`⊤` = infeasible, `⊥` = unbounded).
-/

open Matrix

namespace LinearOptimization

/-- A vector of `ℝⁿ` is *integer* if every component is (the coercion of)
an integer — the pure-integer case of the p. 452 integrality clause. -/
def IsIntegerPoint {n : ℕ} (x : Fin n → ℝ) : Prop :=
  ∀ i, ∃ z : ℤ, x i = (z : ℝ)

/-- Mixed integrality (Bertsimas & Tsitsiklis, p. 452): the components indexed by `I` (the
designated integer variables) are integers; the remaining components are
free to be continuous. -/
def IsMixedIntegerPoint {n : ℕ} (I : Set (Fin n)) (x : Fin n → ℝ) : Prop :=
  ∀ i ∈ I, ∃ z : ℤ, x i = (z : ℝ)

/-- Zero-one (binary) integrality (Bertsimas & Tsitsiklis, p. 452): every component is `0`
or `1`. -/
def IsZeroOnePoint {n : ℕ} (x : Fin n → ℝ) : Prop :=
  ∀ i, x i = 0 ∨ x i = 1

/-- **Bertsimas & Tsitsiklis, p. 452.** The feasible set of the mixed integer programming
problem in equality form: `Ax = b`, `x ≥ 0`, and `xᵢ` integer for `i ∈ I`
(the block form `min c'x + d'y, Ax + By = b, x, y ≥ 0, x integer` is the
instance where `I` is the `x`-block of the concatenated variable
vector). -/
def mixedIntegerFeasibleSet {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (I : Set (Fin n)) : Set (Fin n → ℝ) :=
  {x | x ∈ stdPolyhedron A b ∧ IsMixedIntegerPoint I x}

/-- **Bertsimas & Tsitsiklis, §11.4, problem (11.5) (p. 494).** The feasible set of the
inequality-form integer program: `Ax ≥ b`, `Dx ≥ d`, `x` integer. -/
def integerProgramFeasibleSet {m₁ m₂ n : ℕ}
    (A : Matrix (Fin m₁) (Fin n) ℝ) (b : Fin m₁ → ℝ)
    (D : Matrix (Fin m₂) (Fin n) ℝ) (d : Fin m₂ → ℝ) :
    Set (Fin n → ℝ) :=
  {x | x ∈ polyhedron A b ∧ x ∈ polyhedron D d ∧ IsIntegerPoint x}

/-- **Bertsimas & Tsitsiklis, §11.4 (p. 494).** `Z_IP`, the optimal cost of problem (11.5),
`EReal`-valued via `lpValue` (`⊤` = infeasible, `⊥` = unbounded). -/
noncomputable def integerProgramValue {m₁ m₂ n : ℕ} (c : Fin n → ℝ)
    (A : Matrix (Fin m₁) (Fin n) ℝ) (b : Fin m₁ → ℝ)
    (D : Matrix (Fin m₂) (Fin n) ℝ) (d : Fin m₂ → ℝ) : EReal :=
  lpValue c (integerProgramFeasibleSet A b D d)

end LinearOptimization


