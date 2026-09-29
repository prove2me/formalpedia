-- Prove2me | Definitions.Def_BasicSolution
-- name    : BasicSolution
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-04T13:53:48.600342+00:00
-- url     : https://prove2.me/theorems/22c5b6ed-9a54-4cc4-b38b-d0eb1df480e6
-- title:
--   Basic solution and basic feasible solution
-- statement:
--   **(Definition 2.9)** Consider a polyhedron $P$ defined by linear equality and inequality constraints, and let $x^*$ be an element of $\mathbb{R}^n$.
--
--   - **(a)** The vector $x^*$ is a *basic solution* if:
--     - **(i)** all equality constraints are active;
--     - **(ii)** out of the constraints that are active at $x^*$, there are $n$ of them that are linearly independent.
--   - **(b)** If $x^*$ is a basic solution that satisfies all of the constraints, we say that it is a *basic feasible solution*.
--
--   Folded in:
--
--   - two distinct basic solutions to a set of linear constraints in $\mathbb{R}^n$ are said to be *adjacent* if we can find $n-1$ linearly independent constraints that are active at both of them (p. 53, unnumbered);
--   - **(Definition 2.10)** a basic solution $x \in \mathbb{R}^n$ is said to be *degenerate* if more than $n$ of the constraints are active at $x$;
--   - **(Definition 2.11)** for the standard form polyhedron $P = \{x \in \mathbb{R}^n \mid Ax = b,\ x \ge 0\}$ with $A$ having $m$ rows, a basic solution $x$ is degenerate if more than $n - m$ of the components of $x$ are zero.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Definition 2.9, p. 50 (adjacency p. 53; Definitions 2.10-2.11, pp. 58-59)

import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Data.Set.Card
import Definitions.Def_ActiveConstraints

/-!
Basic solutions, basic feasible solutions, degeneracy, and standard-form
bases.

Source: Bertsimas & Tsitsiklis, *Introduction to Linear Optimization*,
Athena Scientific 1997:

- **Definition 2.9 (p. 50).** Consider a polyhedron `P` defined by linear
  equality and inequality constraints, and let `x*` be an element of `ℝⁿ`.
  (a) `x*` is a *basic solution* if (i) all equality constraints are active;
  (ii) out of the constraints that are active at `x*`, there are `n` of them
  that are linearly independent. (b) If `x*` is a basic solution that
  satisfies all of the constraints, it is a *basic feasible solution*.
  (The book notes right after Definition 2.9 that this notion is
  representation-dependent, which is why the constraint family — not the
  solution set — is the argument here.)
- **Definition 2.10 (p. 58).** A basic solution `x ∈ ℝⁿ` is *degenerate* if
  more than `n` of the constraints are active at `x`.
- Standard-form vocabulary (§2.3 pp. 54–55): basic indices `B(1), …, B(m)`,
  basic columns `A_{B(1)}, …, A_{B(m)}` (required linearly independent, so
  they form a basis of `ℝᵐ`), the invertible `m × m` *basis matrix* `B`.
- **Definition 2.11 (p. 59).** For the standard-form polyhedron
  `P = {x ∈ ℝⁿ | Ax = b, x ≥ 0}` with `m` the number of rows of `A`, a basic
  solution `x` is *degenerate* if more than `n − m` of the components of `x`
  are zero.
-/

open Matrix

namespace LinearOptimization

/-- **B&T Definition 2.9(a) (p. 50).** `x` is a basic solution of the
constraint family `C`: every equality constraint is active at `x`, and among
the constraints active at `x` there are `n` linearly independent ones
(linear independence of constraints = linear independence of their vectors
`aᵢ`, cf. the remark after Theorem 2.2, p. 49). -/
def IsBasicSolution {ι : Type} {n : ℕ} (C : ι → LinearConstraint n)
    (x : Fin n → ℝ) : Prop :=
  (∀ i, (C i).rel = .eq → (C i).IsActiveAt x) ∧
  ∃ s : Finset ι, s.card = n ∧ (∀ i ∈ s, (C i).IsActiveAt x) ∧
    LinearIndependent ℝ (fun i : s => (C i.1).a)

/-- **B&T Definition 2.9(b) (p. 50).** A basic solution that satisfies all
of the constraints. -/
def IsBasicFeasibleSolution {ι : Type} {n : ℕ} (C : ι → LinearConstraint n)
    (x : Fin n → ℝ) : Prop :=
  IsBasicSolution C x ∧ x ∈ constraintSet C

/-- **B&T Definition 2.10 (p. 58).** A basic solution is degenerate if more
than `n` of the constraints are active at it. -/
def IsDegenerateBasicSolution {ι : Type} {n : ℕ}
    (C : ι → LinearConstraint n) (x : Fin n → ℝ) : Prop :=
  IsBasicSolution C x ∧ n < {i | (C i).IsActiveAt x}.ncard

/-- Standard-form basis (B&T §2.3 pp. 54–55): an injective choice of basic
indices `B : Fin m ↪ Fin n` whose basic columns `A_{B(1)}, …, A_{B(m)}` are
linearly independent (hence form a basis of `ℝᵐ`). -/
def IsStdBasis {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (B : Fin m ↪ Fin n) : Prop :=
  LinearIndependent ℝ (fun i => Aᵀ (B i))

/-- The `m × m` basis matrix obtained by arranging the basic columns next to
each other (B&T p. 55; invertible when `IsStdBasis A B`). -/
def basisMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (B : Fin m ↪ Fin n) : Matrix (Fin m) (Fin m) ℝ :=
  A.submatrix id B

/-- **B&T Definition 2.11 (p. 59).** For the standard-form polyhedron
`{x | Ax = b, x ≥ 0}` with `A` an `m × n` matrix: a basic solution `x` is
degenerate if more than `n − m` of its components are zero. -/
def IsStdDegenerateBasicSolution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  IsBasicSolution (stdFormSystem A b) x ∧ n - m < {j | x j = 0}.ncard

end LinearOptimization


