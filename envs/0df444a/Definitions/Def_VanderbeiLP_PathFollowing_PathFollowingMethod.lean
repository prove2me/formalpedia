-- Prove2me | Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod
-- name    : VanderbeiLP_PathFollowing_PathFollowingMethod
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T19:42:23.975985+00:00
-- url     : https://prove2.me/theorems/18283048-9e35-4b03-acca-1158754a96ac
-- title:
--   The path-following method of Fig. 18.1 with step length (18.7): norms, $\rho$, $\sigma$, $\gamma$, Newton system, one iteration
-- statement:
--   Fix integers $m, n \ge 0$, an $m \times n$ real matrix $A$, and vectors $b \in \mathbb{R}^m$, $c \in \mathbb{R}^n$. The linear program is
--
--   $$\text{maximize } c^Tx \quad \text{subject to } Ax + w = b,\ x, w \ge 0,$$
--
--   with dual $\text{minimize } b^Ty$ subject to $A^Ty - z = c$, $y, z \ge 0$. A **primal–dual point** is a quadruple $(x, w, y, z)$ with $x, z \in \mathbb{R}^n$ and $w, y \in \mathbb{R}^m$; the same format holds a **step direction** $(\Delta x, \Delta w, \Delta y, \Delta z)$. Write $(x, w, y, z) > 0$ when every component of all four vectors is strictly positive, and $X, W, Y, Z$ for the diagonal matrices with the entries of $x, w, y, z$ on the diagonal; $e$ is the all-ones vector.
--
--   This file defines:
--
--   1. the norms $\|v\|_1 = \sum_j |v_j|$ and $\|v\|_\infty = \max_j |v_j|$ (with $\|v\|_\infty = 0$ for the empty vector);
--   2. the **primal infeasibility** $\rho = b - Ax - w$, the **dual infeasibility** $\sigma = c - A^Ty + z$ and the **complementarity** $\gamma = z^Tx + y^Tw$;
--   3. the **barrier parameter** $\mu = \delta\,\gamma/(n + m)$, for a parameter $\delta$;
--   4. the **Newton system** (18.1)–(18.4): $(\Delta x, \Delta w, \Delta y, \Delta z)$ is a step direction at $(x, w, y, z)$ when
--   $$A\Delta x + \Delta w = \rho, \quad A^T\Delta y - \Delta z = \sigma, \quad Z\Delta x + X\Delta z = \mu e - XZe, \quad W\Delta y + Y\Delta w = \mu e - YWe;$$
--   5. the **step length** (18.7), for a parameter $r$:
--   $$\theta = r\left(\max_{i,j}\left\{\left|\frac{\Delta x_j}{x_j}\right|, \left|\frac{\Delta w_i}{w_i}\right|, \left|\frac{\Delta y_i}{y_i}\right|, \left|\frac{\Delta z_j}{z_j}\right|\right\}\right)^{-1} \wedge 1,$$
--   where $a \wedge b = \min(a, b)$, and $\theta = 1$ when the maximum is $0$;
--   6. **one iteration** of the path-following method of Fig. 18.1 with this step length: from a point $(x, w, y, z) > 0$, using a solution $(\Delta x, \Delta w, \Delta y, \Delta z)$ of the Newton system, move to $(x + \theta\Delta x, w + \theta\Delta w, y + \theta\Delta y, z + \theta\Delta z)$.
--
--   These are the objects of the convergence analysis of Chapter 18: every result of the mission is a statement about this iteration and the three measures of progress $\|\rho\|_1$, $\|\sigma\|_1$ and $\gamma$.
--
--   **Formalization Note** Vectors are `Fin n → ℝ` and `Fin m → ℝ`, and $A$ is a `Matrix (Fin m) (Fin n) ℝ`; the point is a structure `PDPoint m n` with fields `x w y z`. The sup-norm is `⨆ j, |v j|`, which over the finite index set is the maximum and is `0` for the empty vector. The book writes $r \cdot 0^{-1} \wedge 1$ when all ratios vanish, which it reads as $1$; since Lean's `r / 0 = 0`, this case is written out as `if max = 0 then 1`. The Newton system is not assumed to have a unique solution: an iteration may use any solution. The parameters $0 < \delta < 1$ and $0 < r < 1$ are not built into the definitions; they are hypotheses of every theorem.
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, pp. 269–275 (PDF pp. 279–285): step (3) p. 269; Eqs. (18.1)–(18.4) p. 270; μ p. 272; Fig. 18.1 p. 273; norms p. 274; ρ, σ, γ p. 274; step length Eq. (18.7) p. 275

import Mathlib

open Matrix

namespace VanderbeiLP.PathFollowing

/-- The 1-norm `‖v‖₁ = ∑ⱼ |vⱼ|` (Vanderbei, p. 274, the `p = 1` case of the `p`-norm). -/
def norm1 {k : ℕ} (v : Fin k → ℝ) : ℝ :=
  ∑ j, |v j|

/-- The sup-norm `‖v‖∞ = maxⱼ |vⱼ|` (Vanderbei, p. 274). The index set is finite, so for
`k ≥ 1` this is the maximum of the finitely many values `|vⱼ|`; for `k = 0` (the empty
vector) it is `0`. -/
noncomputable def normInf {k : ℕ} (v : Fin k → ℝ) : ℝ :=
  ⨆ j, |v j|

/-- A primal–dual point `(x, w, y, z)` for the LP `maximize cᵀx s.t. Ax + w = b, x, w ≥ 0`
and its dual `minimize bᵀy s.t. Aᵀy − z = c, y, z ≥ 0` (Vanderbei, Ch. 18, p. 269):
`x, z ∈ ℝⁿ`, `w, y ∈ ℝᵐ`. The same structure also holds a step direction
`(Δx, Δw, Δy, Δz)`. -/
structure PDPoint (m n : ℕ) where
  x : Fin n → ℝ
  w : Fin m → ℝ
  y : Fin m → ℝ
  z : Fin n → ℝ

/-- `(x, w, y, z) > 0`: every component of every one of the four vectors is strictly
positive (p. 269, footnote on p. 148). -/
def PDPoint.Positive {m n : ℕ} (p : PDPoint m n) : Prop :=
  (∀ j, 0 < p.x j) ∧ (∀ i, 0 < p.w i) ∧ (∀ i, 0 < p.y i) ∧ ∀ j, 0 < p.z j

/-- The point `(x + θΔx, w + θΔw, y + θΔy, z + θΔz)` reached from `p` by a step of
length `θ` in the direction `d = (Δx, Δw, Δy, Δz)` (p. 269, step (3)). -/
def PDPoint.advance {m n : ℕ} (p : PDPoint m n) (θ : ℝ) (d : PDPoint m n) : PDPoint m n :=
  ⟨p.x + θ • d.x, p.w + θ • d.w, p.y + θ • d.y, p.z + θ • d.z⟩

/-- Primal infeasibility `ρ = b − Ax − w` (p. 270, p. 274). -/
def primalInfeas {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (p : PDPoint m n) : Fin m → ℝ :=
  b - A *ᵥ p.x - p.w

/-- Dual infeasibility `σ = c − Aᵀy + z` (p. 270, p. 274). -/
def dualInfeas {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (p : PDPoint m n) : Fin n → ℝ :=
  c - Aᵀ *ᵥ p.y + p.z

/-- Complementarity `γ = zᵀx + yᵀw` (p. 273, Fig. 18.1; p. 274). -/
def complementarity {m n : ℕ} (p : PDPoint m n) : ℝ :=
  p.z ⬝ᵥ p.x + p.y ⬝ᵥ p.w

/-- The barrier parameter chosen by the method, `μ = δ γ / (n + m)` (p. 272 and Fig. 18.1).
(When `n + m = 0` both `γ` and this value are `0`.) -/
noncomputable def barrierParam {m n : ℕ} (δ : ℝ) (p : PDPoint m n) : ℝ :=
  δ * complementarity p / ((n : ℝ) + m)

/-- `d = (Δx, Δw, Δy, Δz)` solves the Newton system (18.1)–(18.4) at the point
`p = (x, w, y, z)` with `μ = δ γ / (n + m)`:
`AΔx + Δw = ρ`, `AᵀΔy − Δz = σ`, `ZΔx + XΔz = μe − XZe`, `WΔy + YΔw = μe − YWe`
(p. 270 and Fig. 18.1, p. 273). No uniqueness of the solution is assumed. -/
def IsNewtonDirection {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (δ : ℝ) (p d : PDPoint m n) : Prop :=
  A *ᵥ d.x + d.w = primalInfeas A b p ∧
  Aᵀ *ᵥ d.y - d.z = dualInfeas A c p ∧
  (∀ j, p.z j * d.x j + p.x j * d.z j = barrierParam δ p - p.x j * p.z j) ∧
  (∀ i, p.w i * d.y i + p.y i * d.w i = barrierParam δ p - p.y i * p.w i)

/-- The largest absolute ratio
`max(‖X⁻¹Δx‖∞, ‖W⁻¹Δw‖∞, ‖Y⁻¹Δy‖∞, ‖Z⁻¹Δz‖∞)
  = max_{i,j} {|Δxⱼ/xⱼ|, |Δwᵢ/wᵢ|, |Δyᵢ/yᵢ|, |Δzⱼ/zⱼ|}` of (18.7), p. 275. -/
noncomputable def maxAbsRatio {m n : ℕ} (p d : PDPoint m n) : ℝ :=
  max (max (normInf fun j => d.x j / p.x j) (normInf fun i => d.w i / p.w i))
    (max (normInf fun i => d.y i / p.y i) (normInf fun j => d.z j / p.z j))

/-- The step length (18.7) of the convergence analysis (p. 275):
`θ = r · (max_{i,j}{|Δxⱼ/xⱼ|, |Δwᵢ/wᵢ|, |Δyᵢ/yᵢ|, |Δzⱼ/zⱼ|})⁻¹ ∧ 1`, where `a ∧ b = min(a, b)`.
When the maximum is `0` the book's value is `r · ∞ ∧ 1 = 1`; this case is written out
explicitly (Lean's `r / 0 = 0` would otherwise give `θ = 0`). -/
noncomputable def stepLength {m n : ℕ} (r : ℝ) (p d : PDPoint m n) : ℝ :=
  if maxAbsRatio p d = 0 then 1 else min (r / maxAbsRatio p d) 1

/-- One iteration of the path-following method of Fig. 18.1 (p. 273) with the step length
(18.7) (p. 275), from the current point `p` to the next point `p'`, using the step
direction `d`: the current point is strictly positive, `d` solves the Newton system
(18.1)–(18.4) with `μ = δγ/(n + m)`, and `p' = p + θ d` with `θ = stepLength r p d`. -/
def IsPathFollowingStep {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (δ r : ℝ) (p d p' : PDPoint m n) : Prop :=
  p.Positive ∧ IsNewtonDirection A b c δ p d ∧ p' = p.advance (stepLength r p d) d

end VanderbeiLP.PathFollowing


