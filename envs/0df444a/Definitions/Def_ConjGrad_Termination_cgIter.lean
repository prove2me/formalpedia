-- Prove2me | Definitions.Def_ConjGrad_Termination_cgIter
-- name    : ConjGrad_Termination_cgIter
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T21:47:29.708625+00:00
-- url     : https://prove2.me/theorems/da9ea802-99bd-40e4-86b8-604aaf86c4a7
-- title:
--   The conjugate gradient method (3:1): iterates $x_i$, residuals $r_i$, directions $p_i$
-- statement:
--   Let $A$ be a real $n \times n$ matrix, $k \in \mathbb{R}^n$ a right-hand side, and $x_0 \in \mathbb{R}^n$ an arbitrary initial estimate of the solution of $Ax = k$. Write $(x, y) = x_1y_1 + \cdots + x_ny_n$ for the scalar product and $|x|^2 = (x, x)$.
--
--   The **conjugate gradient method** (cg-method) of Hestenes and Stiefel produces estimates $x_i$, residuals $r_i$ and directions $p_i$, $i = 0, 1, 2, \dots$, as follows. The initial step is
--
--   $$p_0 = r_0 = k - Ax_0. \qquad (3{:}1\text{a})$$
--
--   Having $x_i$, $r_i$ and $p_i$, the general routine computes, in this order,
--
--   $$a_i = \frac{|r_i|^2}{(p_i, Ap_i)}, \quad x_{i+1} = x_i + a_i p_i, \quad r_{i+1} = r_i - a_i A p_i, \quad b_i = \frac{|r_{i+1}|^2}{|r_i|^2}, \quad p_{i+1} = r_{i+1} + b_i p_i. \qquad (3{:}1\text{b–f})$$
--
--   The step length $a_i$ is also recorded separately as a function of the current triple $(x_i, r_i, p_i)$, so that other statements can refer to it.
--
--   The residual $r_{i+1}$ is computed by the update (3:1d), not as $k - Ax_{i+1}$; that the two agree is a theorem, not part of the definition. This is the method whose finite termination is the goal of the mission.
--
--   **Formalization Note** Vectors are functions `Fin n → ℝ`, the scalar product is `dotProduct` and $Ax$ is `Matrix.mulVec`. Indices are 0-based, as in the paper. There is no stopping test: Lean's real division returns $0$ when the denominator is $0$, so once $r_m = 0$ one gets $b_{m-1} = 0$, $p_m = 0$, $a_m = 0/0 = 0$, and the sequence stays at $x_m$ with $r_i = p_i = 0$ for all $i \ge m$. The state of one step is the structure `CGState` with fields `x`, `r`, `p`; `cgA A s` is the step length (3:1b) at state `s`, `cgStep` is one general-routine step, and `cgIter A k x₀ i` is the state after $i$ steps.
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), https://doi.org/10.6028/jres.049.044, p. 411, eq. (3:1a)–(3:1f) and the description of the cg-method following (3:2b); repeated as eq. (5:1a)–(5:1f), p. 414

import Mathlib

open Matrix

namespace ConjGrad.Termination

/-- The data carried by one step of the conjugate gradient method (Hestenes–Stiefel 1952,
§3, p. 411): the current estimate `x = xᵢ` of the solution `h`, its residual `r = rᵢ`, and
the current direction `p = pᵢ`. Vectors are `Fin n → ℝ`. -/
structure CGState (n : ℕ) where
  /-- the estimate `xᵢ` of the solution `h` -/
  x : Fin n → ℝ
  /-- the residual `rᵢ` -/
  r : Fin n → ℝ
  /-- the direction `pᵢ` -/
  p : Fin n → ℝ

/-- The step length (3:1b): `aᵢ = |rᵢ|² / (pᵢ, Apᵢ)`. Lean's real division returns `0` when
`(pᵢ, Apᵢ) = 0`. -/
noncomputable def cgA {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : CGState n) : ℝ :=
  (s.r ⬝ᵥ s.r) / (s.p ⬝ᵥ (A *ᵥ s.p))

/-- One general routine step of the cg-method, formulas (3:1b)–(3:1f) in this order:
`aᵢ = |rᵢ|²/(pᵢ,Apᵢ)`, `xᵢ₊₁ = xᵢ + aᵢpᵢ`, `rᵢ₊₁ = rᵢ − aᵢApᵢ`, `bᵢ = |rᵢ₊₁|²/|rᵢ|²`,
`pᵢ₊₁ = rᵢ₊₁ + bᵢpᵢ`. There is no stopping test: once `rₘ = 0` the division by zero gives
`bₘ₋₁ = 0`, `pₘ = 0`, `aₘ = 0`, and the iteration stays at `xₘ` with zero residual and
direction. -/
noncomputable def cgStep {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : CGState n) : CGState n :=
  let a := cgA A s                           -- (3:1b)
  let x' := s.x + a • s.p                    -- (3:1c)
  let r' := s.r - a • (A *ᵥ s.p)             -- (3:1d)
  let b := (r' ⬝ᵥ r') / (s.r ⬝ᵥ s.r)         -- (3:1e)
  let p' := r' + b • s.p                     -- (3:1f)
  ⟨x', r', p'⟩

/-- The cg-method (3:1) started at an arbitrary estimate `x₀`: step `0` is (3:1a),
`p₀ = r₀ = k − Ax₀`, and step `i + 1` applies `cgStep` to step `i`. Indices are 0-based as
in the paper. -/
noncomputable def cgIter {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k x₀ : Fin n → ℝ) :
    ℕ → CGState n
  | 0 => ⟨x₀, k - A *ᵥ x₀, k - A *ᵥ x₀⟩
  | i + 1 => cgStep A (cgIter A k x₀ i)

end ConjGrad.Termination


