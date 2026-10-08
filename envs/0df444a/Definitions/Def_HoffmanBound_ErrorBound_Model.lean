-- Prove2me | Definitions.Def_HoffmanBound_ErrorBound_Model
-- name    : HoffmanBound_ErrorBound_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T09:20:58.689887+00:00
-- url     : https://prove2.me/theorems/a851b321-11cb-450a-b2ea-aa096bf7a81d
-- title:
--   System Ax ≦ b, positive part (2), positive homogeneous functions (3), Euclidean nearest point, the sets E and K′
-- statement:
--   This file fixes the objects of Hoffman's paper on approximate solutions of linear inequalities.
--
--   Let $A=(a_{ij})$ be a real $m\times n$ matrix with rows $A_1,\dots,A_m$ and let $b\in\mathbb R^m$. The system (1) is
--   $$
--   A_i\cdot x=a_{i1}x_1+\dots+a_{in}x_n\le b_i\qquad(i=1,\dots,m),
--   $$
--   briefly $Ax\le b$, and $\Omega=\{x\in\mathbb R^n : Ax\le b\}$ is its **solution set**. The system is **consistent** when $\Omega\neq\emptyset$.
--
--   1. **Positive part (2).** For a real $a$, $a^+=a$ if $a\ge 0$ and $a^+=0$ if $a<0$; for a vector $y=(y_1,\dots,y_k)$, $y^+=(y_1^+,\dots,y_k^+)$.
--   2. **Positive homogeneous function (3).** A function $F_k:\mathbb R^k\to\mathbb R$ is positive homogeneous if it is continuous and (i) $F_k(x)\ge 0$, with $F_k(x)=0$ if and only if $x=0$; (ii) $\alpha\ge 0$ implies $F_k(\alpha x)=\alpha F_k(x)$. No triangle inequality, symmetry or convexity is assumed.
--   3. **Nearest point.** A point $y$ is a point of a set $\Omega'\subseteq\mathbb R^n$ nearest to $x$ if $y\in\Omega'$ and $(x-y)\cdot(x-y)\le(x-z)\cdot(x-z)$ for every $z\in\Omega'$ (Euclidean distance).
--   4. **Rows on $S$.** For a set $S\subseteq\{1,\dots,m\}$ of rows (half spaces of (1)), $M=M_S$ is the $m\times n$ matrix obtained from $A$ by substituting $0$ for the rows not in $S$, and for $y\in\mathbb R^m$, $\bar y$ keeps the coordinates $y_i$, $i\in S$, and replaces the others by $0$.
--   5. **Active set.** For $y\in\mathbb R^n$, $S(y)=\{i : A_i\cdot y=b_i\}$, the half spaces of (1) whose bounding hyperplane contains $y$.
--   6. **The set $E$ of Lemma 3.** With $\Omega_0=\{z : Mz\le 0\}$, $E$ is the set of $x$ with $x\notin\Omega_0$ such that the origin is the point of $\Omega_0$ nearest to $x$.
--   7. **The set $K'$ of Lemma 4.** $K'$ is the cone spanned by the row vectors $M_1,\dots,M_m$ of $M$, with the origin deleted: all $x\neq 0$ of the form $\lambda_1M_1+\dots+\lambda_mM_m$ with $\lambda_i\ge 0$.
--
--   These objects are shared by every statement of the mission: the main theorem, Lemmas 1–4 and the explicit bounds (8)–(10).
--
--   **Formalization Note** Vectors are functions `Fin k → ℝ`, the system is `A *ᵥ x ≤ b` in the componentwise order, and $y^+$ is `posPartVec y = fun i => max (y i) 0`. The paper never names the distance in "nearest"; its proof of Lemma 4 computes with $(x-z)\cdot(x-z)$, so the distance is Euclidean and is written with the dot product (Mathlib's `dist` on `Fin n → ℝ` would be the sup distance). $S$ is a `Finset (Fin m)` of row indices, and $M$ keeps all $m$ rows, so $Mx\in\mathbb R^m$.
-- source:
--   Hoffman, On Approximate Solutions of Systems of Linear Inequalities, J. Res. Nat. Bur. Standards 49 (1952), pp. 263–264 (PDF pp. 1–2): system (1), definitions (2) and (3), Lemmas 1–4

import Mathlib

namespace HoffmanBound.ErrorBound

open Matrix

/-- Hoffman 1952, p. 263, (3): a *positive homogeneous function* `F_k` on `k`-space is a real
continuous function with (i) `F_k(x) ≥ 0`, and `F_k(x) = 0` if and only if `x = 0`; and
(ii) `α ≥ 0` implies `F_k(α x) = α F_k(x)`. Nothing else (no triangle inequality, no symmetry,
no convexity) is assumed. -/
def IsPosHomogeneous {k : ℕ} (F : (Fin k → ℝ) → ℝ) : Prop :=
  Continuous F ∧ (∀ x, 0 ≤ F x) ∧ (∀ x, F x = 0 ↔ x = 0) ∧
    ∀ α : ℝ, 0 ≤ α → ∀ x, F (α • x) = α * F x

/-- Hoffman 1952, p. 263, (2): the positive part of a vector, `y⁺ = (y₁⁺, …, y_k⁺)` with
`a⁺ = a` if `a ≥ 0` and `a⁺ = 0` if `a < 0`. -/
def posPartVec {k : ℕ} (y : Fin k → ℝ) : Fin k → ℝ := fun i => max (y i) 0

/-- Hoffman 1952, p. 263, (1): the set `Ω` of solutions of the system `Ax ≤ b`, i.e. of
`A_i · x ≤ b_i` for `i = 1, …, m` (componentwise order). -/
def solutionSet {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {x | A *ᵥ x ≤ b}

/-- `y` is a point of `Ω` nearest to `x` in the Euclidean distance: `y ∈ Ω` and
`(x - y)·(x - y) ≤ (x - z)·(x - z)` for every `z ∈ Ω`. -/
def IsNearest {n : ℕ} (Ω : Set (Fin n → ℝ)) (x y : Fin n → ℝ) : Prop :=
  y ∈ Ω ∧ ∀ z ∈ Ω, (x - y) ⬝ᵥ (x - y) ≤ (x - z) ⬝ᵥ (x - z)

/-- The matrix `M` obtained from `A` by substituting `0` for the rows not in `S` (it keeps all
`m` rows). -/
def rowsOn {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin m)) :
    Matrix (Fin m) (Fin n) ℝ :=
  Matrix.of fun i => if i ∈ S then A i else 0

/-- The vector `ȳ` obtained from `y` by substituting `0` for the components not in `S`
(Lemma 1; also `b̄` in the proof of the theorem). -/
def restrictVec {m : ℕ} (S : Finset (Fin m)) (y : Fin m → ℝ) : Fin m → ℝ :=
  fun i => if i ∈ S then y i else 0

/-- The set `S` of the half spaces `A_i · z ≤ b_i` whose bounding hyperplane contains `y`,
i.e. the indices with `A_i · y = b_i` (Lemma 2). -/
noncomputable def activeSet {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
    Finset (Fin m) :=
  Finset.univ.filter fun i => (A *ᵥ y) i = b i

/-- Lemma 3: for `M = rowsOn A S` and the cone `Ω = {z | M z ≤ 0}`, the set `E` of all `x` such
that (i) `x ∉ Ω` and (ii) the origin is the point of `Ω` nearest to `x`. -/
def setE {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin m)) : Set (Fin n → ℝ) :=
  {x | x ∉ solutionSet (rowsOn A S) 0 ∧ IsNearest (solutionSet (rowsOn A S) 0) x 0}

/-- Lemma 4: `K'`, the cone spanned by the row vectors `M_1, …, M_m` of `M = rowsOn A S`, with
the origin deleted: all `x ≠ 0` of the form `λ₁ M₁ + ⋯ + λ_m M_m` with every `λ_i ≥ 0`. -/
def conePrime {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin m)) :
    Set (Fin n → ℝ) :=
  {x | x ≠ 0 ∧ ∃ c : Fin m → ℝ, (∀ i, 0 ≤ c i) ∧ x = ∑ i, c i • rowsOn A S i}

end HoffmanBound.ErrorBound


