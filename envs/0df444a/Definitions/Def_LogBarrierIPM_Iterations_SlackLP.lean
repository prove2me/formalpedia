-- Prove2me | Definitions.Def_LogBarrierIPM_Iterations_SlackLP
-- name    : LogBarrierIPM_Iterations_SlackLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T13:45:36.545057+00:00
-- url     : https://prove2.me/theorems/d1281595-2168-402f-8422-96f94b464e66
-- title:
--   The primal-dual pair LP(A,b,c), DualLP(A,b,c) in slack form, the sets $\mathcal F$, $\mathcal F^\circ$, the duality measure (2) and the wide neighborhood (5)
-- statement:
--   Let $A$ be a real $m\times n$ matrix, $b\in\mathbb R^m$, $c\in\mathbb R^n$, and set $N := n+m$. The linear program in slack form and its dual are
--   $$\mathrm{LP}(A,b,c):\ \text{minimize } \langle c,x\rangle \text{ subject to } Ax+w=b,\ (x,w)\in\mathbb R^{n+m}_+,$$
--   $$\mathrm{DualLP}(A,b,c):\ s-A^\top y=c,\ (s,y)\in\mathbb R^{n+m}_+ .$$
--   A **primal-dual point** is $z=(x,w,s,y)\in\mathbb R^{2N}$ with $x,s\in\mathbb R^n$ and $w,y\in\mathbb R^m$. This module defines:
--
--   1. the **primal-dual feasible set** $\mathcal F=\{z\ge 0:\ Ax+w=b,\ s-A^\top y=c\}$;
--   2. the set of **strictly feasible** points $\mathcal F^\circ=\{z>0:\ Ax+w=b,\ s-A^\top y=c\}$ (all $2N$ coordinates positive);
--   3. the **duality measure** (2)
--   $$\bar\mu(z)=\frac1N\big(\langle x,s\rangle+\langle w,y\rangle\big);$$
--   4. the **wide neighborhood** (5) of the central path, for a precision parameter $\theta$,
--   $$\mathcal N^{-\infty}_\theta=\Big\{z\in\mathcal F^\circ:\ \begin{pmatrix} xs\\ wy\end{pmatrix}\ge(1-\theta)\,\bar\mu(z)\,e\Big\},$$
--   where $xs$ and $wy$ are Hadamard (coordinatewise) products and $e$ is the all-ones vector of $\mathbb R^N$: every product $x_js_j$ and $w_iy_i$ is at least $(1-\theta)\bar\mu(z)$. There is no upper bound on the products.
--
--   These are the objects in which the paper's lower bound on path-following interior point methods is stated: a method is only assumed to move along segments that stay inside $\mathcal N^{-\infty}_\theta$.
--
--   **Formalization Note** A point is the product type $(\mathbb R^n)\times(\mathbb R^m)\times(\mathbb R^n)\times(\mathbb R^m)$ (components $x,w,s,y$), so it carries the vector-space structure used for segments. The dual equation is written $s-A^\top y=c$ with Mathlib's transpose. The page writes "maximize $\langle b,y\rangle$" for the dual; no statement of this mission uses the dual objective. $\bar\mu$ divides by $N=n+m$ as a real number.
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 4, §2, LP(A,b,c), DualLP(A,b,c), F°, eq. (2); p. 5, eq. (5) and Proposition 1 (F)

import Mathlib

open Matrix

namespace LogBarrierIPM.Iterations

/-- A primal-dual point `z = (x, w, s, y) ∈ ℝ^{2N}` (`N = n + m`) of the pair `LP(A, b, c)`,
`DualLP(A, b, c)` of Allamigeon–Benchimol–Gaubert–Joswig, §2, p. 4: `x, s ∈ ℝⁿ`, `w, y ∈ ℝᵐ`.
The components are `z.1 = x`, `z.2.1 = w`, `z.2.2.1 = s`, `z.2.2.2 = y`. -/
abbrev PDPoint (n m : ℕ) : Type := (Fin n → ℝ) × (Fin m → ℝ) × (Fin n → ℝ) × (Fin m → ℝ)

/-- The primal-dual feasible set `F = {z = (x, w, s, y) ≥ 0 : Ax + w = b, s − Aᵀy = c}` of
`LP(A, b, c)` (minimize `⟨c, x⟩` s.t. `Ax + w = b`, `(x, w) ≥ 0`) and
`DualLP(A, b, c)` (`s − Aᵀy = c`, `(s, y) ≥ 0`), §2, p. 4. -/
def primalDualFeasible {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) : Set (PDPoint n m) :=
  {z | A *ᵥ z.1 + z.2.1 = b ∧ z.2.2.1 - Aᵀ *ᵥ z.2.2.2 = c ∧
    (∀ j, 0 ≤ z.1 j) ∧ (∀ i, 0 ≤ z.2.1 i) ∧ (∀ j, 0 ≤ z.2.2.1 j) ∧ ∀ i, 0 ≤ z.2.2.2 i}

/-- The set `F° = {z = (x, w, s, y) > 0 : Ax + w = b, s − Aᵀy = c}` of strictly feasible
primal-dual points, §2, p. 4 (all `2N` coordinates strictly positive). -/
def strictlyFeasible {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) : Set (PDPoint n m) :=
  {z | A *ᵥ z.1 + z.2.1 = b ∧ z.2.2.1 - Aᵀ *ᵥ z.2.2.2 = c ∧
    (∀ j, 0 < z.1 j) ∧ (∀ i, 0 < z.2.1 i) ∧ (∀ j, 0 < z.2.2.1 j) ∧ ∀ i, 0 < z.2.2.2 i}

/-- The duality measure (2), p. 4: `μ̄(z) = (⟨x, s⟩ + ⟨w, y⟩) / N` with `N = n + m`. -/
noncomputable def dualityMeasure {n m : ℕ} (z : PDPoint n m) : ℝ :=
  (z.1 ⬝ᵥ z.2.2.1 + z.2.1 ⬝ᵥ z.2.2.2) / ((n + m : ℕ) : ℝ)

/-- The wide neighborhood (5), p. 5:
`N^{−∞}_θ = {z ∈ F° : (xs, wy) ≥ (1 − θ) μ̄(z) e}`, i.e. `x_j s_j ≥ (1 − θ) μ̄(z)` for every
`j` and `w_i y_i ≥ (1 − θ) μ̄(z)` for every `i` (Hadamard products, one-sided bound only). -/
def wideNeighborhood {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (θ : ℝ) : Set (PDPoint n m) :=
  {z | z ∈ strictlyFeasible A b c ∧
    (∀ j, (1 - θ) * dualityMeasure z ≤ z.1 j * z.2.2.1 j) ∧
    ∀ i, (1 - θ) * dualityMeasure z ≤ z.2.1 i * z.2.2.2 i}

end LogBarrierIPM.Iterations


