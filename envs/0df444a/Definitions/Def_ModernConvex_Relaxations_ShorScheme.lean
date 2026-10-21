-- Prove2me | Definitions.Def_ModernConvex_Relaxations_ShorScheme
-- name    : ModernConvex_Relaxations_ShorScheme
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:33:02.105866+00:00
-- url     : https://prove2.me/theorems/dcec6bf3-d4fb-43b4-bead-6c50c40e1f66
-- title:
--   Quadratically constrained problem (4.3.5), its semidefinite lower bound (4.3.9) and Shor's relaxation (4.3.11)
-- statement:
--   This file fixes the objects of Shor's semidefinite relaxation scheme (Ben-Tal–Nemirovski, §4.3.1, pp. 161–164).
--
--   1. For a matrix $A \in \mathbb R^{n\times n}$, a vector $b \in \mathbb R^n$ and a number $c$, the **inhomogeneous quadratic form** is $g(x) = x^TAx + 2b^Tx + c$, and the **bordered matrix** of (4.3.8) is the $(n+1)\times(n+1)$ matrix
--   $$\begin{pmatrix} c & b^T \\ b & A\end{pmatrix}.$$
--   2. A **quadratically constrained problem** (4.3.5) is given by symmetric matrices $A_0, A_1, \dots, A_m \in \mathbb R^{n\times n}$, vectors $b_0, \dots, b_m$ and numbers $c_0, \dots, c_m$:
--   $$\min_{x\in\mathbb R^n}\ f_0(x) = x^TA_0x + 2b_0^Tx + c_0 \quad\text{s.t.}\quad f_i(x) = x^TA_ix + 2b_i^Tx + c_i = 0,\ i = 1,\dots,m.$$
--   Its **optimal value** is the infimum of $f_0$ over the feasible set, taken in $[-\infty, +\infty]$ ($+\infty$ if no $x$ is feasible, $-\infty$ if $f_0$ is unbounded below on it).
--   3. A pair $(\zeta, \lambda) \in \mathbb R \times \mathbb R^m$ is **feasible for (4.3.9)** if
--   $$\begin{pmatrix} c_0 + \sum_i \lambda_i c_i - \zeta & b_0^T + \sum_i \lambda_i b_i^T \\ b_0 + \sum_i \lambda_i b_i & A_0 + \sum_i \lambda_i A_i\end{pmatrix} \succeq 0,$$
--   and the optimal value of (4.3.9) is the supremum of $\zeta$ over such pairs, in $[-\infty, +\infty]$ ($-\infty$ if there are none).
--   4. With the lifted matrices $\bar A_i = \begin{pmatrix} c_i & b_i^T \\ b_i & A_i\end{pmatrix}$, $i = 0, \dots, m$, a symmetric $(n+1)\times(n+1)$ matrix $X$ is **feasible for Shor's relaxation (4.3.11)** if $\operatorname{Tr}(\bar A_iX) = 0$ for $i = 1, \dots, m$, $X \succeq 0$ and $X_{11} = 1$; the optimal value of (4.3.11) is the infimum of $\operatorname{Tr}(\bar A_0X)$ over such $X$, in $[-\infty, +\infty]$.
--
--   These are the objects of the Simple lemma and of Propositions 4.3.1 and 4.3.2.
--
--   **Formalization Note** Vectors are `Fin n → ℝ`; the $(n+1)\times(n+1)$ matrices are indexed by `Unit ⊕ Fin n`, the index `Sum.inl ()` playing the role of the book's first row and column, so $X_{11}$ is `X (Sum.inl ()) (Sum.inl ())`. Positive semidefiniteness is Mathlib's `Matrix.PosSemidef`, which includes symmetry. The three optimal values are infima/suprema in `EReal`, a complete lattice, so the empty and unbounded cases take the values $\pm\infty$ the book uses and no junk value occurs. The multipliers $\lambda$ are named `lam`. Symmetry of $A_0, \dots, A_m$ is a separate predicate `IsSymmetric`, passed as a hypothesis.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 161 (4.3.5), p. 162 (4.3.8), p. 163 (4.3.9), p. 164 (4.3.11)

import Mathlib

open Matrix

namespace ModernConvex.Relaxations

/-- The inhomogeneous quadratic form `g(x) = xᵀAx + 2bᵀx + c` (Ben-Tal–Nemirovski, p. 162). -/
def quadForm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (c : ℝ) (x : Fin n → ℝ) :
    ℝ :=
  x ⬝ᵥ (A *ᵥ x) + 2 * (b ⬝ᵥ x) + c

/-- The `(n + 1) × (n + 1)` matrix `(c bᵀ; b A)` of (4.3.8), p. 162. Its rows and columns are
indexed by `Unit ⊕ Fin n`: the index `Sum.inl ()` is the book's first ("northwestern") row and
column, the indices `Sum.inr i` are the remaining `n`. -/
def borderedMatrix {n : ℕ} (c : ℝ) (b : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ :=
  Matrix.fromBlocks (Matrix.of fun _ _ => c) (Matrix.of fun _ j => b j)
    (Matrix.of fun i _ => b i) A

/-- The data of the quadratically constrained problem (4.3.5), p. 161:
`minimize f₀(x) = xᵀA₀x + 2b₀ᵀx + c₀` over `x ∈ ℝⁿ`
`s.t. fᵢ(x) = xᵀAᵢx + 2bᵢᵀx + cᵢ = 0, i = 1, …, m`.
The constraint index `i = 1, …, m` is `i : Fin m`. -/
structure QuadraticProblem (n m : ℕ) where
  A₀ : Matrix (Fin n) (Fin n) ℝ
  b₀ : Fin n → ℝ
  c₀ : ℝ
  A : Fin m → Matrix (Fin n) (Fin n) ℝ
  b : Fin m → Fin n → ℝ
  c : Fin m → ℝ

namespace QuadraticProblem

variable {n m : ℕ}

/-- The matrices of the problem are symmetric, as the book's quadratic forms are. -/
def IsSymmetric (P : QuadraticProblem n m) : Prop :=
  P.A₀.IsHermitian ∧ ∀ i, (P.A i).IsHermitian

/-- The objective `f₀(x) = xᵀA₀x + 2b₀ᵀx + c₀` of (4.3.5). -/
def f₀ (P : QuadraticProblem n m) (x : Fin n → ℝ) : ℝ :=
  quadForm P.A₀ P.b₀ P.c₀ x

/-- The constraint function `fᵢ(x) = xᵀAᵢx + 2bᵢᵀx + cᵢ` of (4.3.5). -/
def f (P : QuadraticProblem n m) (i : Fin m) (x : Fin n → ℝ) : ℝ :=
  quadForm (P.A i) (P.b i) (P.c i) x

/-- `x` is feasible for (4.3.5): `fᵢ(x) = 0` for `i = 1, …, m`. -/
def Feasible (P : QuadraticProblem n m) (x : Fin n → ℝ) : Prop :=
  ∀ i, P.f i x = 0

/-- The optimal value of (4.3.5) in `[−∞, +∞]`: the infimum of `f₀` over the feasible set
(`+∞` when the problem is infeasible, `−∞` when it is unbounded below). -/
noncomputable def optimalValue (P : QuadraticProblem n m) : EReal :=
  ⨅ (x : Fin n → ℝ) (_ : P.Feasible x), ((P.f₀ x : ℝ) : EReal)

/-- `(ζ, λ) ∈ ℝ × ℝᵐ` is feasible for (4.3.9), p. 163:
`( c₀ + Σᵢ λᵢcᵢ − ζ , b₀ᵀ + Σᵢ λᵢbᵢᵀ ; b₀ + Σᵢ λᵢbᵢ , A₀ + Σᵢ λᵢAᵢ ) ⪰ 0`. -/
def DualBoundFeasible (P : QuadraticProblem n m) (ζ : ℝ) (lam : Fin m → ℝ) : Prop :=
  (borderedMatrix (P.c₀ + ∑ i, lam i * P.c i - ζ) (P.b₀ + ∑ i, lam i • P.b i)
    (P.A₀ + ∑ i, lam i • P.A i)).PosSemidef

/-- The optimal value of the semidefinite program (4.3.9), `max_{ζ,λ} ζ` over its feasible set,
in `[−∞, +∞]` (`−∞` when (4.3.9) is infeasible). -/
noncomputable def dualBoundValue (P : QuadraticProblem n m) : EReal :=
  ⨆ (ζ : ℝ) (lam : Fin m → ℝ) (_ : P.DualBoundFeasible ζ lam), ((ζ : ℝ) : EReal)

/-- The lifted matrix `Ā₀ = (c₀ b₀ᵀ; b₀ A₀)` of (4.3.11), p. 164. -/
def liftedObjective (P : QuadraticProblem n m) : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ :=
  borderedMatrix P.c₀ P.b₀ P.A₀

/-- The lifted matrices `Āᵢ = (cᵢ bᵢᵀ; bᵢ Aᵢ)`, `i = 1, …, m`, of (4.3.11), p. 164. -/
def liftedConstraint (P : QuadraticProblem n m) (i : Fin m) :
    Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ :=
  borderedMatrix (P.c i) (P.b i) (P.A i)

/-- `X` is feasible for Shor's semidefinite relaxation (4.3.11), p. 164:
`Tr(ĀᵢX) = 0, i = 1, …, m; X ⪰ 0; X₁₁ = 1`. -/
def ShorFeasible (P : QuadraticProblem n m) (X : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ) :
    Prop :=
  (∀ i, (P.liftedConstraint i * X).trace = 0) ∧ X.PosSemidef ∧ X (Sum.inl ()) (Sum.inl ()) = 1

/-- The optimal value of (4.3.11), `min_X Tr(Ā₀X)` over its feasible set, in `[−∞, +∞]`. -/
noncomputable def shorValue (P : QuadraticProblem n m) : EReal :=
  ⨅ (X : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℝ) (_ : P.ShorFeasible X),
    (((P.liftedObjective * X).trace : ℝ) : EReal)

end QuadraticProblem

end ModernConvex.Relaxations


