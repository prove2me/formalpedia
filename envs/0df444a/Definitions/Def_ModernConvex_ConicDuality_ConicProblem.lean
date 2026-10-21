-- Prove2me | Definitions.Def_ModernConvex_ConicDuality_ConicProblem
-- name    : ModernConvex_ConicDuality_ConicProblem
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:31:49.661097+00:00
-- url     : https://prove2.me/theorems/f416491d-4d27-4c6b-8f7f-a37b81bfbefb
-- title:
--   Conic problem $\min\{c^Tx \mid Ax - b \ge_{\mathbf K} 0\}$, its conic dual, the dual cone, and their feasibility, boundedness and optimality notions
-- statement:
--   Fix integers $m, n \ge 0$, a set $\mathbf K \subset \mathbb R^m$, an $m\times n$ matrix $A$, a right-hand side $b \in \mathbb R^m$ and an objective $c \in \mathbb R^n$. Write $a \ge_{\mathbf K} b$ for $a - b \in \mathbf K$ and $a >_{\mathbf K} b$ for $a - b \in \operatorname{int}\mathbf K$. The **conic problem** and its **conic dual** are
--   $$\text{(CP)}\quad \min_x\left\{c^Tx \;\middle|\; Ax - b \ge_{\mathbf K} 0\right\}, \qquad \text{(D)}\quad \max_\lambda\left\{b^T\lambda \;\middle|\; A^T\lambda = c,\ \lambda \ge_{\mathbf K_*} 0\right\}.$$
--   The file defines, following pp. 1–2 and 45–57 of the book:
--
--   1. $\mathbf K$ is a **convex cone** if it is nonempty, closed under addition, and $t a \in \mathbf K$ whenever $a \in \mathbf K$ and $t \ge 0$; it is **pointed** if $a \in \mathbf K$ and $-a \in \mathbf K$ imply $a = 0$. A **good cone** (the standing assumption of p. 46) is a pointed, closed convex cone with a nonempty interior.
--   2. The **dual cone** $\mathbf K_* = \{\lambda \in \mathbb R^m : \lambda^Ta \ge 0\ \ \forall a \in \mathbf K\}$ (p. 51).
--   3. **Assumption A** (p. 53): the columns of $A$ are linearly independent, i.e. $Ax = Ax'$ implies $x = x'$.
--   4. $x$ is **feasible** for (CP) if $Ax - b \in \mathbf K$; (CP) is **strictly feasible** if $Ax - b \in \operatorname{int}\mathbf K$ for some $x$; (CP) is **bounded below** if there is $L \in \mathbb R$ with $c^Tx \ge L$ for every feasible $x$ (so an infeasible problem is bounded below, as on p. 1); $x$ is an **optimal solution** if it is feasible and $c^Tx \le c^Tx'$ for every feasible $x'$; (CP) is **solvable** if it has an optimal solution; $v$ is the **optimal value** of (CP) if it is the greatest lower bound of $\{c^Tx : x \text{ feasible}\}$.
--   5. Dually, $\lambda$ is **feasible** for (D) if $A^T\lambda = c$ and $\lambda \in \mathbf K_*$; (D) is **strictly feasible** if some $\lambda \in \operatorname{int}\mathbf K_*$ has $A^T\lambda = c$; (D) is **bounded above** if $b^T\lambda \le U$ for some $U$ and all dual feasible $\lambda$; optimal solutions, solvability and the optimal value (least upper bound of $\{b^T\lambda : \lambda \text{ dual feasible}\}$) are defined as for (CP) with max in place of min.
--
--   These are the objects of the conic duality theorem (Theorem 2.4.1) and the results around it.
--
--   **Formalization Note** Vectors are functions `Fin m → ℝ` with the product (= Euclidean) topology, $c^Tx$ is `c ⬝ᵥ x`, $Ax$ is `A *ᵥ x`. The optimal values $c^*, b^* \in [-\infty, +\infty]$ never appear as Lean reals with a junk default: only through the predicates "$v$ is the optimal value" (`IsGLB`/`IsLUB` of the set of feasible objective values), which no real satisfies when the problem is infeasible or unbounded. The good-cone conditions and Assumption A are separate predicates, passed as explicit hypotheses in the theorems.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, pp. 1–2 (bounded below, solvable), p. 45 (pointed convex cone), p. 46 (standing assumption on K, (CP)), pp. 51–52 (K∗, (D)), p. 53 (Assumption A), p. 57 (strict feasibility)

import Mathlib

open Matrix

namespace ModernConvex.ConicDuality

/-- A convex cone in `ℝᵐ` in the sense of Ben-Tal–Nemirovski, p. 45 (conditions 1 and 2): a
nonempty set closed under addition and under multiplication by nonnegative reals. -/
def IsConvexCone {m : ℕ} (K : Set (Fin m → ℝ)) : Prop :=
  K.Nonempty ∧ (∀ a ∈ K, ∀ a' ∈ K, a + a' ∈ K) ∧ (∀ a ∈ K, ∀ t : ℝ, 0 ≤ t → t • a ∈ K)

/-- `K` is pointed (p. 45, condition 3): `a ∈ K` and `−a ∈ K` imply `a = 0`. -/
def IsPointedSet {m : ℕ} (K : Set (Fin m → ℝ)) : Prop :=
  ∀ a : Fin m → ℝ, a ∈ K → -a ∈ K → a = 0

/-- The standing assumption on the cone of a conic problem (p. 46): `K` is a pointed and closed
convex cone with a nonempty interior. -/
def IsGoodCone {m : ℕ} (K : Set (Fin m → ℝ)) : Prop :=
  IsConvexCone K ∧ IsPointedSet K ∧ IsClosed K ∧ (interior K).Nonempty

/-- The cone dual to `K` (p. 51): `K∗ = {λ ∈ ℝᵐ | λᵀa ≥ 0 ∀ a ∈ K}`. -/
def dualCone {m : ℕ} (K : Set (Fin m → ℝ)) : Set (Fin m → ℝ) :=
  {l | ∀ a ∈ K, 0 ≤ l ⬝ᵥ a}

/-- Assumption A (p. 53): the `m × n` matrix `A` of a conic problem has full column rank, i.e.
the map `x ↦ Ax` has trivial kernel. -/
def AssumptionA {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  Function.Injective A.mulVec

/-- `x` is feasible for `(CP) : min { cᵀx | Ax − b ≥_K 0 }` (p. 46): `Ax − b ∈ K`. -/
def PrimalFeasible {m n : ℕ} (K : Set (Fin m → ℝ)) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  A *ᵥ x - b ∈ K

/-- `(CP)` is strictly feasible (p. 57): `Ax − b >_K 0`, i.e. `Ax − b ∈ int K`, for some `x`. -/
def PrimalStrictlyFeasible {m n : ℕ} (K : Set (Fin m → ℝ)) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) : Prop :=
  ∃ x : Fin n → ℝ, A *ᵥ x - b ∈ interior K

/-- `(CP)` is bounded below (the convention of p. 1): it is infeasible, or its objective `cᵀx` is bounded below on
the feasible set. -/
def PrimalBoundedBelow {m n : ℕ} (K : Set (Fin m → ℝ)) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) : Prop :=
  ∃ L : ℝ, ∀ x, PrimalFeasible K A b x → L ≤ c ⬝ᵥ x

/-- `x` is an optimal solution of `(CP)`: feasible, and `cᵀx ≤ cᵀx'` for every feasible `x'`. -/
def IsPrimalOptimal {m n : ℕ} (K : Set (Fin m → ℝ)) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (x : Fin n → ℝ) : Prop :=
  PrimalFeasible K A b x ∧ ∀ x', PrimalFeasible K A b x' → c ⬝ᵥ x ≤ c ⬝ᵥ x'

/-- `(CP)` is solvable (the convention of p. 2): it has an optimal solution. -/
def PrimalSolvable {m n : ℕ} (K : Set (Fin m → ℝ)) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) : Prop :=
  ∃ x, IsPrimalOptimal K A b c x

/-- `v` is the (finite) optimal value `c∗ = inf { cᵀx | Ax − b ≥_K 0 }` of `(CP)`: the greatest
lower bound of the objective values at feasible points. No real `v` qualifies when `(CP)` is
infeasible (`c∗ = +∞`) or unbounded below (`c∗ = −∞`). -/
def IsPrimalOptimalValue {m n : ℕ} (K : Set (Fin m → ℝ)) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (v : ℝ) : Prop :=
  IsGLB {t : ℝ | ∃ x, PrimalFeasible K A b x ∧ t = c ⬝ᵥ x} v

/-- `λ` is feasible for the conic dual `(D) : max { bᵀλ | Aᵀλ = c, λ ≥_{K∗} 0 }` (p. 52). -/
def DualFeasible {m n : ℕ} (K : Set (Fin m → ℝ)) (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) (l : Fin m → ℝ) : Prop :=
  Aᵀ *ᵥ l = c ∧ l ∈ dualCone K

/-- `(D)` is strictly feasible (p. 57): some `λ >_{K∗} 0`, i.e. `λ ∈ int K∗`, has `Aᵀλ = c`. -/
def DualStrictlyFeasible {m n : ℕ} (K : Set (Fin m → ℝ)) (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) : Prop :=
  ∃ l : Fin m → ℝ, Aᵀ *ᵥ l = c ∧ l ∈ interior (dualCone K)

/-- `(D)` is bounded above: it is infeasible, or its objective `bᵀλ` is bounded above on its
feasible set. -/
def DualBoundedAbove {m n : ℕ} (K : Set (Fin m → ℝ)) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) : Prop :=
  ∃ U : ℝ, ∀ l, DualFeasible K A c l → b ⬝ᵥ l ≤ U

/-- `λ` is an optimal solution of `(D)`: dual feasible, and `bᵀλ' ≤ bᵀλ` for every dual feasible
`λ'`. -/
def IsDualOptimal {m n : ℕ} (K : Set (Fin m → ℝ)) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (l : Fin m → ℝ) : Prop :=
  DualFeasible K A c l ∧ ∀ l', DualFeasible K A c l' → b ⬝ᵥ l' ≤ b ⬝ᵥ l

/-- `(D)` is solvable: it has an optimal solution. -/
def DualSolvable {m n : ℕ} (K : Set (Fin m → ℝ)) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) : Prop :=
  ∃ l, IsDualOptimal K A b c l

/-- `v` is the (finite) optimal value `b∗ = sup { bᵀλ | Aᵀλ = c, λ ≥_{K∗} 0 }` of `(D)`: the
least upper bound of the dual objective values at dual feasible points. -/
def IsDualOptimalValue {m n : ℕ} (K : Set (Fin m → ℝ)) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (v : ℝ) : Prop :=
  IsLUB {t : ℝ | ∃ l, DualFeasible K A c l ∧ t = b ⬝ᵥ l} v

end ModernConvex.ConicDuality


