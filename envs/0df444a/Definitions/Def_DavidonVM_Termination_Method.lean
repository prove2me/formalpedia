-- Prove2me | Definitions.Def_DavidonVM_Termination_Method
-- name    : DavidonVM_Termination_Method
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:41:58.816993+00:00
-- url     : https://prove2.me/theorems/7bce03be-e0d3-49e8-bade-a8c9c6af1e3f
-- title:
--   The quadratic with constant Hessian G, its gradient (6), and Davidon's rank-one variable-metric method (2)–(3) with a = (M − N)⁻¹
-- statement:
--   This file fixes the objects of the Appendix of Davidon's *Variable Metric Method for Minimization* (pp. 16–17).
--
--   Points and gradients are vectors of $\mathbb R^n$ and matrices are real $n\times n$ matrices. For a matrix $G$, a point $\xi\in\mathbb R^n$ and a constant $c$, the **quadratic with constant Hessian $G$** is
--   $$
--   f(x)=\tfrac12\,(x-\xi)^{\mathsf T}G\,(x-\xi)+c ,
--   $$
--   and the **gradient field** of the Appendix, display (6), is
--   $$
--   \nabla(x)=G\,(x-\xi).
--   $$
--
--   For a gradient field $g$ (a map $\mathbb R^n\to\mathbb R^n$), a sequence of points $x_0,x_1,\dots$ and a sequence of trial matrices $H_0,H_1,\dots$, write $\nabla_k=g(x_k)$ and define the two scalars of p. 16 at iteration $k$:
--   $$
--   N_k=\nabla_{k+1}^{\mathsf T}H_k\nabla_{k+1},\qquad M_k=\nabla_{k+1}^{\mathsf T}H_k\nabla_k .
--   $$
--
--   A **run of the method (2)–(3)** with coefficients $a_0,a_1,\dots$ is a pair of sequences satisfying, for every $k\ge 0$,
--   $$
--   x_{k+1}=x_k-H_k\nabla_k,\qquad H_{k+1}=H_k+a_k\,(H_k\nabla_{k+1})(H_k\nabla_{k+1})^{\mathsf T}.
--   $$
--   The first equation is the full step (2) (no line search); the second is the rank-one update (3).
--
--   A **run on the quadratic** is a run for the gradient field (6), $g(x)=G(x-\xi)$, with the coefficient of footnote 2,
--   $$
--   a_k=(M_k-N_k)^{-1}.
--   $$
--
--   These objects are the shared vocabulary of every statement of the mission: the gradient (6), the secant property (8), the persistence (7) of eigenvectors with eigenvalue one, and the termination claim after (8).
--
--   **Formalization Note** Vectors are `Fin n → ℝ` with 0-based indices, matrices `Matrix (Fin n) (Fin n) ℝ`; $u^{\mathsf T}Hv$ is `u ⬝ᵥ (H *ᵥ v)` and $(Hg)(Hg)^{\mathsf T}$ is `vecMulVec (H *ᵥ g) (H *ᵥ g)`. The paper's letter $N$ denotes both the number of variables and the scalar $\nabla^{+}H\nabla^{+}$; in Lean the dimension is `n` and the scalars are `Nval`, `Mval`. Lean's inverse of a real number gives $0^{-1}=0$, so when $M_k=N_k$ the update leaves $H_k$ unchanged; every statement that uses the update therefore assumes $M_k\ne N_k$ for the steps it needs. The paper's stopping rule ("provided that $N$ is greater than some preassigned $\varepsilon$", p. 17) is not modelled: the run predicate constrains every $k$. The paper uses the "+" superscript for updated quantities; here $x^{+}$, $H^{+}$, $\nabla^{+}$ at iteration $k$ are $x_{k+1}$, $H_{k+1}$, $\nabla_{k+1}$.
-- source:
--   Davidon, Variable Metric Method for Minimization, SIAM J. Optim. 1(1) (1991), pp. 16–17, Appendix (2), (3), (6) and footnote 2

import Mathlib

namespace DavidonVM.Termination

open Matrix

/-- Points and gradients of ℝⁿ, as plain coordinate functions `Fin n → ℝ`
(indices are 0-based; the paper's μ, ν run over 1, …, N). -/
abbrev Vec (n : ℕ) := Fin n → ℝ

/-- Real n × n matrices (the Hessian G and the trial matrices H). -/
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- The quadratic with constant Hessian `G` and stationary point `ξ`:
`f(x) = ½ (x − ξ)ᵀ G (x − ξ) + c` (Davidon 1991, Appendix, p. 17: "When the G is constant"). -/
noncomputable def quad {n : ℕ} (G : Mat n) (ξ : Vec n) (c : ℝ) (x : Vec n) : ℝ :=
  (1 / 2 : ℝ) * ((x - ξ) ⬝ᵥ (G *ᵥ (x - ξ))) + c

/-- Appendix (6), p. 17: the gradient field `∇ = G(x − ξ)`. -/
def grad {n : ℕ} (G : Mat n) (ξ : Vec n) (x : Vec n) : Vec n :=
  G *ᵥ (x - ξ)

/-- The scalar `N = ∇⁺ᵀ H ∇⁺` of Appendix p. 16 at iteration `k`, for a gradient field `g`:
`∇⁺ = g (x (k+1))` and `H = H k`. -/
def Nval {n : ℕ} (g : Vec n → Vec n) (x : ℕ → Vec n) (H : ℕ → Mat n) (k : ℕ) : ℝ :=
  g (x (k + 1)) ⬝ᵥ (H k *ᵥ g (x (k + 1)))

/-- The scalar `M = ∇⁺ᵀ H ∇` of Appendix p. 16 at iteration `k`, for a gradient field `g`:
`∇⁺ = g (x (k+1))`, `∇ = g (x k)` and `H = H k`. -/
def Mval {n : ℕ} (g : Vec n → Vec n) (x : ℕ → Vec n) (H : ℕ → Mat n) (k : ℕ) : ℝ :=
  g (x (k + 1)) ⬝ᵥ (H k *ᵥ g (x k))

/-- A run of the Appendix method (2)–(3), p. 16, for a gradient field `g` with coefficients `a k`:
`x_{k+1} = x_k − H_k ∇_k` (the full step (2), no line search) and
`H_{k+1} = H_k + a_k (H_k ∇_{k+1})(H_k ∇_{k+1})ᵀ` (the rank-one update (3)),
where `∇_k = g (x k)`. There is no stopping rule: the iteration continues for every `k`. -/
def IsRunWith {n : ℕ} (g : Vec n → Vec n) (a : ℕ → ℝ) (x : ℕ → Vec n) (H : ℕ → Mat n) :
    Prop :=
  ∀ k, x (k + 1) = x k - H k *ᵥ g (x k) ∧
    H (k + 1) = H k + a k • vecMulVec (H k *ᵥ g (x (k + 1))) (H k *ᵥ g (x (k + 1)))

/-- The method on the quadratic with constant Hessian `G` and stationary point `ξ`:
the gradient field is (6), `∇ = G(x − ξ)`, and the coefficient is footnote 2's
`a_k = (M_k − N_k)⁻¹` (Lean's `⁻¹` gives `0` when `M_k = N_k`). -/
def IsQuadRun {n : ℕ} (G : Mat n) (ξ : Vec n) (x : ℕ → Vec n) (H : ℕ → Mat n) : Prop :=
  IsRunWith (grad G ξ) (fun k => (Mval (grad G ξ) x H k - Nval (grad G ξ) x H k)⁻¹) x H

end DavidonVM.Termination


