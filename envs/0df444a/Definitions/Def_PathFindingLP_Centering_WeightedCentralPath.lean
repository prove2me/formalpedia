-- Prove2me | Definitions.Def_PathFindingLP_Centering_WeightedCentralPath
-- name    : PathFindingLP_Centering_WeightedCentralPath
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T22:34:50.834992+00:00
-- url     : https://prove2.me/theorems/cf6fe38a-fa4d-43f9-a004-8a8840ee5c64
-- title:
--   Slack, interior, weighted Newton step $\vec h_t(\vec x,\vec w)$ and centrality $\delta_t(\vec x,\vec w)$
-- statement:
--   Fix a linear program in inequality form
--   $$\min_{x\in\mathbb R^n:\ Ax\ge b} c^{T}x,$$
--   with constraint matrix $A\in\mathbb R^{m\times n}$ and vectors $b\in\mathbb R^m$, $c\in\mathbb R^n$. This file defines the objects of the weighted path-following framework of Lee and Sidford.
--
--   1. The **slack vector** of $x\in\mathbb R^n$ is $s(x)=Ax-b\in\mathbb R^m$.
--   2. The **interior** of the feasible region is $S^0=\{x\in\mathbb R^n : Ax>b\}$, i.e. every slack is strictly positive.
--   3. A pair $(x,w)$ with $x\in\mathbb R^n$, $w\in\mathbb R^m$ is **feasible** if $x\in S^0$ and every weight $w_i$ is strictly positive.
--   4. The **weighted penalized objective** is $f_t(x,w)=t\,c^Tx-\sum_{i=1}^m w_i\log s(x)_i$ for a path parameter $t\in\mathbb R$.
--   5. Writing $S_x=\mathrm{diag}(s(x))$ and $W=\mathrm{diag}(w)$, the **Newton step** is
--   $$\vec h_t(x,w)=\big(A^TS_x^{-1}WS_x^{-1}A\big)^{-1}\big(t c-A^TS_x^{-1}w\big),$$
--   the Hessian $\nabla^2_{xx}f_t(x,w)=A^TS_x^{-1}WS_x^{-1}A$ applied inversely to the gradient $\nabla_x f_t(x,w)=tc-A^TS_x^{-1}w$.
--   6. For a square matrix $M$ write $\|v\|_M=\sqrt{v^TMv}$. The **centrality** of $(x,w)$ is the Newton step measured in the Hessian norm,
--   $$\delta_t(x,w)=\big\|\vec h_t(x,w)\big\|_{A^TS_x^{-1}WS_x^{-1}A}.$$
--
--   The centrality measures how far $x$ is from minimizing $f_t(\cdot,w)$, i.e. from the weighted central path; it is the quantity every step of the method is designed to keep small.
--
--   **Formalization Note** Vectors are functions `Fin n → ℝ`, `Fin m → ℝ`; $S_x^{-1}$ is the diagonal matrix of the reciprocals $1/s(x)_i$, and the matrix inverse is Mathlib's `Matrix.inv`, which returns $0$ on a singular matrix. Every theorem using these definitions therefore assumes that $A$ has full column rank, which (with positive slacks and weights) makes $A^TS_x^{-1}WS_x^{-1}A$ invertible. The Newton step and centrality are defined by the explicit formulas (3) and (4), not through derivatives of $f_t$; of the two equal forms of (4), the first (Hessian norm of $\vec h_t$) is used. $f_t$ itself is recorded for reference only.
-- source:
--   Lee, Sidford, Path Finding Methods for Linear Programming, FOCS 2014, pp. 424–433 (DOI 10.1109/FOCS.2014.52): p. 424, §I, eq. (1) (the LP); p. 425, §II.A (S^0 and the slack vector s(x)); p. 427, §IV, eq. (2) (f_t and feasible pairs); p. 428, §IV.A, eqs. (3) (Newton step) and (4) (centrality)

import Mathlib

open Matrix

namespace PathFindingLP.Centering

variable {m n : ℕ}

/-- The slack vector `s(x) = A x - b` of the linear program `min { cᵀx : A x ≥ b }`
(Lee–Sidford, FOCS 2014, §II.A, p. 425). -/
def slack (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) : Fin m → ℝ :=
  A *ᵥ x - b

/-- The interior of the feasible region, `S⁰ = {x ∈ ℝⁿ : A x > b}` (componentwise strict),
(§II.A, p. 425). -/
def interiorS0 (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ i, 0 < slack A b x i}

/-- A pair `(x, w)` is feasible if `x ∈ S⁰` and `w ∈ ℝᵐ_{>0}` (§IV, p. 427). -/
def IsFeasible (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ)
    (w : Fin m → ℝ) : Prop :=
  x ∈ interiorS0 A b ∧ ∀ i, 0 < w i

/-- The weighted penalized objective `f_t(x, w) = t · cᵀx - ∑ᵢ wᵢ log s(x)ᵢ`, eq. (2), p. 427.
It is recorded for reference: the Newton step and the centrality below are given by the
explicit formulas of (3) and (4). -/
noncomputable def weightedObjective (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (t : ℝ) (x : Fin n → ℝ) (w : Fin m → ℝ) : ℝ :=
  t * (c ⬝ᵥ x) - ∑ i, w i * Real.log (slack A b x i)

/-- The matrix `Aᵀ S⁻¹ W S⁻¹ A` with `S = diag(s)`, `W = diag(w)`, where `S⁻¹` is the diagonal
matrix of the reciprocals `1 / sᵢ`. At `s = s(x)` it is the Hessian `∇²ₓₓ f_t(x, w)`. -/
noncomputable def weightedGram (A : Matrix (Fin m) (Fin n) ℝ) (s w : Fin m → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Aᵀ * diagonal (fun i => (s i)⁻¹) * diagonal w * diagonal (fun i => (s i)⁻¹) * A

/-- The gradient `∇ₓ f_t(x, w) = t c - Aᵀ S_x⁻¹ w`. -/
noncomputable def weightedGradient (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (t : ℝ) (x : Fin n → ℝ) (w : Fin m → ℝ) : Fin n → ℝ :=
  t • c - Aᵀ *ᵥ (diagonal (fun i => (slack A b x i)⁻¹) *ᵥ w)

/-- The Newton step, eq. (3), p. 428:
`h_t(x, w) = (Aᵀ S_x⁻¹ W S_x⁻¹ A)⁻¹ (t c - Aᵀ S_x⁻¹ w)`. -/
noncomputable def newtonStep (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (t : ℝ) (x : Fin n → ℝ) (w : Fin m → ℝ) : Fin n → ℝ :=
  (weightedGram A (slack A b x) w)⁻¹ *ᵥ weightedGradient A b c t x w

/-- The norm `‖v‖_M = √(vᵀ M v)` induced by a square matrix `M`. -/
noncomputable def matNorm {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (v : Fin k → ℝ) : ℝ :=
  Real.sqrt (v ⬝ᵥ (M *ᵥ v))

/-- The centrality, eq. (4), p. 428: the Newton step measured in the Hessian norm,
`δ_t(x, w) = ‖h_t(x, w)‖_{∇²ₓₓ f_t(x, w)}`. -/
noncomputable def centrality (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (t : ℝ) (x : Fin n → ℝ) (w : Fin m → ℝ) : ℝ :=
  matNorm (weightedGram A (slack A b x) w) (newtonStep A b c t x w)

end PathFindingLP.Centering


