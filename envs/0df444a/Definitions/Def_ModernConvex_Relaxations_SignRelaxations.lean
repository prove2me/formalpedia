-- Prove2me | Definitions.Def_ModernConvex_Relaxations_SignRelaxations
-- name    : ModernConvex_Relaxations_SignRelaxations
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:33:00.923009+00:00
-- url     : https://prove2.me/theorems/a5c9c38f-326b-4bb3-8559-214f663c56d5
-- title:
--   Quadratic maximization over ±1 vectors, MAXCUT, their semidefinite relaxations, asin[X] and the constant 0.87856…
-- statement:
--   This file fixes the objects of §4.3.3–4.3.4 of Ben-Tal–Nemirovski (pp. 170–174).
--
--   1. $S_n$ is the set of vectors $x \in \mathbb R^n$ with every coordinate equal to $1$ or $-1$.
--   2. A symmetric matrix $X \in \mathbb R^{n\times n}$ is **feasible for the relaxations (4.3.15) and (4.3.18)** if $X = X^T \succeq 0$ and $X_{ii} = 1$ for $i = 1,\dots,n$.
--   3. For $A \in \mathbb R^{n\times n}$, $\mathrm{OPT}$ is the optimal value of (4.3.17) and $\mathrm{SDP}$ that of its relaxation (4.3.18):
--   $$\mathrm{OPT} = \max_{x\in S_n} x^TAx, \qquad \mathrm{SDP} = \max\{\operatorname{Tr}(AX) : X = X^T \succeq 0,\ X_{ii} = 1,\ i = 1,\dots,n\}.$$
--   4. $\operatorname{asin}[X]$ is the matrix with the elements $\operatorname{asin}(X_{ij})$.
--   5. For weights $a_{ij}$, $\mathrm{OPT}$ is the optimal value of the MAXCUT problem (4.3.14) and $\mathrm{SDP}$ that of its relaxation (4.3.15):
--   $$\mathrm{OPT} = \max_x\Big\{\tfrac14\sum_{i,j=1}^n a_{ij}(1 - x_ix_j) : x_i^2 = 1,\ i = 1,\dots,n\Big\}, \qquad \mathrm{SDP} = \max\Big\{\tfrac14\sum_{i,j=1}^n a_{ij}(1 - X_{ij}) : X = X^T \succeq 0,\ X_{ii} = 1\Big\}.$$
--   6. The **Goemans–Williamson constant** $\alpha = 0.87856\ldots$ of p. 172 is the largest $\alpha$ with $\frac{\operatorname{acos}(x)}{\pi} \ge \alpha\,\frac12(1 - x)$ for all $x \in [-1, 1]$, that is
--   $$\alpha = \inf_{-1 \le x < 1} \frac{2\operatorname{acos}(x)}{\pi(1 - x)} = \min_{0 < \theta \le \pi} \frac{2}{\pi}\,\frac{\theta}{1 - \cos\theta}.$$
--
--   These are the objects of Theorem 4.3.1 (Goemans–Williamson), Theorem 4.3.2 (Nesterov) and Lemma 4.3.1.
--
--   **Formalization Note** An optimal value is never a bare `sSup`: "$v$ is the optimal value" is the predicate that $v$ is the least upper bound (`IsLUB`) of the objective over the feasible set. Both feasible sets are nonempty (any $x \in S_n$; the identity matrix) and the objective is bounded on them ($S_n$ is finite; $|X_{ij}| \le 1$ on the relaxed set), so these optimal values exist and are attained. $\alpha$ is defined as `sInf` of the image of $[-1, 1)$ under $x \mapsto 2\operatorname{acos}(x)/(\pi(1-x))$, a nonempty set of nonnegative reals, so `sInf` is its genuine infimum; it is not rounded.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 170 (4.3.14), (4.3.15), p. 172 (α = 0.87856…), p. 173 (4.3.17), (4.3.18), p. 174 (asin[X])

import Mathlib

open Matrix

namespace ModernConvex.Relaxations

/-- `Sₙ`, the set of `n`-dimensional vectors with coordinates `±1` (Ben-Tal–Nemirovski,
pp. 172–173). -/
def signVectors (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∀ i, x i = 1 ∨ x i = -1}

/-- `X` is feasible for the semidefinite relaxations (4.3.15) and (4.3.18), pp. 170 and 173:
`X = Xᵀ ⪰ 0` and `Xᵢᵢ = 1, i = 1, …, n`. -/
def IsUnitDiagPSD {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  X.PosSemidef ∧ ∀ i, X i i = 1

/-- `v` is the optimal value `OPT` of (4.3.17), p. 173: `max_x {xᵀAx : x ∈ Sₙ}`, i.e. the least
upper bound (here a maximum over a finite nonempty set) of `xᵀAx` over `x ∈ Sₙ`. -/
def IsSignQPValue {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : ℝ) : Prop :=
  IsLUB ((fun x => x ⬝ᵥ (A *ᵥ x)) '' signVectors n) v

/-- `v` is the optimal value `SDP` of the semidefinite relaxation (4.3.18), p. 173:
`maximize Tr(AX) s.t. X = Xᵀ ⪰ 0, Xᵢᵢ = 1`, i.e. the least upper bound of `Tr(AX)` over the
feasible set. -/
def IsSignSDPValue {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : ℝ) : Prop :=
  IsLUB ((fun X => (A * X).trace) '' {X | IsUnitDiagPSD X}) v

/-- `asin[X]`, the matrix with the elements `asin(Xᵢⱼ)` (p. 174). -/
noncomputable def asinMatrix {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => Real.arcsin (X i j)

/-- The objective of the MAXCUT problem (4.3.14), p. 170: `¼ Σ_{i,j=1}^n aᵢⱼ(1 − xᵢxⱼ)`. -/
noncomputable def maxcutObjective {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  (1 / 4 : ℝ) * ∑ i, ∑ j, a i j * (1 - x i * x j)

/-- `v` is the optimal value `OPT` of the MAXCUT problem (4.3.14), p. 170:
`max_x {¼ Σ_{i,j} aᵢⱼ(1 − xᵢxⱼ) : xᵢ² = 1, i = 1, …, n}`. -/
def IsMaxcutValue {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) (v : ℝ) : Prop :=
  IsLUB (maxcutObjective a '' {x | ∀ i, x i ^ 2 = 1}) v

/-- The objective of the semidefinite relaxation (4.3.15), p. 170: `¼ Σ_{i,j} aᵢⱼ(1 − Xᵢⱼ)`. -/
noncomputable def maxcutRelaxationObjective {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (1 / 4 : ℝ) * ∑ i, ∑ j, a i j * (1 - X i j)

/-- `v` is the optimal value `SDP` of the semidefinite relaxation (4.3.15) of MAXCUT, p. 170:
`maximize ¼ Σ aᵢⱼ(1 − Xᵢⱼ) s.t. X = [Xᵢⱼ] = Xᵀ ⪰ 0, Xᵢᵢ = 1, i = 1, …, n`. -/
def IsMaxcutSDPValue {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) (v : ℝ) : Prop :=
  IsLUB (maxcutRelaxationObjective a '' {X | IsUnitDiagPSD X}) v

/-- The Goemans–Williamson constant `α = 0.87856…` of p. 172: the largest `α` with
`acos(x)/π ≥ α · ½(1 − x)` for all `x ∈ [−1, 1]`, i.e.
`α = inf_{−1 ≤ x < 1} 2 acos(x) / (π (1 − x))`. The set is nonempty and bounded below by `0`,
so the infimum is a genuine real number (the infimum is attained). -/
noncomputable def gwConstant : ℝ :=
  sInf ((fun x : ℝ => 2 * Real.arccos x / (Real.pi * (1 - x))) '' Set.Ico (-1 : ℝ) 1)

end ModernConvex.Relaxations


