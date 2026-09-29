-- Prove2me | Definitions.Def_ConjGrad_ErrorDecrease_cgIter
-- name    : ConjGrad_ErrorDecrease_cgIter
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T21:53:30.327788+00:00
-- url     : https://prove2.me/theorems/ebc9eb19-e33b-4824-9b02-9e212343378b
-- title:
--   The conjugate gradient method (5:1) of Hestenes and Stiefel
-- statement:
--   Let $A$ be a real $n\times n$ matrix and let $k\in\mathbb{R}^n$ be the right-hand side of the linear system $Ax=k$. Write $(x,y)=x_1y_1+\cdots+x_ny_n$ for the scalar product and $|x|^2=(x,x)$ for the squared length. Starting from an arbitrary estimate $x_0\in\mathbb{R}^n$, the **cg-method** of Hestenes and Stiefel produces estimates $x_i$, residuals $r_i$ and direction vectors $p_i$ by
--
--   $$
--   \begin{aligned}
--   p_0 &= r_0 = k - Ax_0, &&(5{:}1a)\\
--   a_i &= \frac{|r_i|^2}{(p_i,Ap_i)}, &&(5{:}1b)\\
--   x_{i+1} &= x_i + a_i p_i, &&(5{:}1c)\\
--   r_{i+1} &= r_i - a_i A p_i, &&(5{:}1d)\\
--   b_i &= \frac{|r_{i+1}|^2}{|r_i|^2}, &&(5{:}1e)\\
--   p_{i+1} &= r_{i+1} + b_i p_i. &&(5{:}1f)
--   \end{aligned}
--   $$
--
--   The definition packages the triple $(x_i,r_i,p_i)$ as a state, gives the step length $a_i$ as a function of the state, and defines the whole sequence $i\mapsto(x_i,r_i,p_i)$, $i=0,1,2,\dots$, by exactly these formulas, computed in this order. The residual $r_{i+1}$ is obtained by the update (5:1d), not recomputed as $k-Ax_{i+1}$, and the scalars are the forms (5:1b) and (5:1e), not the alternative forms (3:2).
--
--   Every result of this mission is stated about this sequence.
--
--   **Formalization Note** Vectors are functions `Fin n → ℝ`, the scalar product is `dotProduct` and $Ax$ is `Matrix.mulVec`. Indices are 0-based, as in the paper. The recursion has no stopping rule: when a denominator vanishes, Lean's convention $t/0=0$ applies. For a symmetric positive definite $A$, once $r_m=0$ the sequence therefore stays at $x_m$ with $r_i=p_i=0$ and $a_i=b_i=0$ for all $i\ge m$, which is the paper's "the algorithm terminates".
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), p. 414, eq. (5:1a)–(5:1f) (identical to (3:1a)–(3:1f), p. 411)

import Mathlib

open Matrix

namespace ConjGrad.ErrorDecrease

/-- The state of the cg-method after `i` steps: the estimate `x = xᵢ` of the solution `h`,
the residual `r = rᵢ` and the direction vector `p = pᵢ`. -/
structure CGState (n : ℕ) where
  /-- the estimate `xᵢ` of `h` -/
  x : Fin n → ℝ
  /-- the residual `rᵢ` -/
  r : Fin n → ℝ
  /-- the direction vector `pᵢ` -/
  p : Fin n → ℝ

/-- The step length `aᵢ = |rᵢ|² / (pᵢ, Apᵢ)` of the cg-method, eq. (5:1b), evaluated at the
state `s = (xᵢ, rᵢ, pᵢ)`. Lean's convention `t / 0 = 0` makes it `0` when `pᵢ = 0`. -/
noncomputable def cgAlpha {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : CGState n) : ℝ :=
  (s.r ⬝ᵥ s.r) / (s.p ⬝ᵥ (A *ᵥ s.p))

/-- The cg-method (5:1) of Hestenes and Stiefel, 0-based and without a stopping guard:
`p₀ = r₀ = k − Ax₀` (5:1a); then `aᵢ = |rᵢ|²/(pᵢ,Apᵢ)` (5:1b), `xᵢ₊₁ = xᵢ + aᵢpᵢ` (5:1c),
`rᵢ₊₁ = rᵢ − aᵢApᵢ` (5:1d), `bᵢ = |rᵢ₊₁|²/|rᵢ|²` (5:1e), `pᵢ₊₁ = rᵢ₊₁ + bᵢpᵢ` (5:1f).
Once `r_m = 0`, Lean's `t / 0 = 0` makes the sequence stay at `x_m` with `r = p = 0`. -/
noncomputable def cgIter {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k x₀ : Fin n → ℝ) :
    ℕ → CGState n
  | 0 => ⟨x₀, k - A *ᵥ x₀, k - A *ᵥ x₀⟩
  | i + 1 =>
    let s := cgIter A k x₀ i
    let a := cgAlpha A s
    let x' := s.x + a • s.p
    let r' := s.r - a • (A *ᵥ s.p)
    let b := (r' ⬝ᵥ r') / (s.r ⬝ᵥ s.r)
    ⟨x', r', r' + b • s.p⟩

end ConjGrad.ErrorDecrease


