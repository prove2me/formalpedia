-- Prove2me | Definitions.Def_NesterovRCD_HighProb_Basic
-- name    : NesterovRCD_HighProb_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T14:20:57.937985+00:00
-- url     : https://prove2.me/theorems/9b334727-ff36-4854-8eed-73977d71201e
-- title:
--   Strong convexity (3.1) in the norm $\|\cdot\|_\beta$ and the regularized objective $f_\mu(x)=f(x)+\frac\mu2\|x-x_0\|_0^2$
-- statement:
--   These two objects of §3 of Nesterov's paper on random coordinate descent are built on the block space $\mathbb R^N=\mathbb R^{n_1}\times\cdots\times\mathbb R^{n_n}$, the weighted norms $\|x\|_\beta=\big[\sum_{i=1}^nL_i^\beta\|x^{(i)}\|_{(i)}^2\big]^{1/2}$ of (2.7) and the other objects of §§1–2 (definition `NesterovRCD.Sublinear.Basic`). Here $L_1,\dots,L_n$ are the coordinate-wise Lipschitz constants and $\|\cdot\|_{(i)}$ the norm of the $i$-th block.
--
--   1. **Strong convexity (3.1).** A function $f:\mathbb R^N\to\mathbb R$ is strongly convex in the norm $\|\cdot\|_\beta$ with parameter $\sigma$ if it is differentiable and for all $x,y\in\mathbb R^N$
--   $$f(y)\ge f(x)+\langle\nabla f(x),y-x\rangle+\tfrac12\sigma\|y-x\|_\beta^2.$$
--   2. **Regularized objective (p. 11).** For $\mu\in\mathbb R$ and a starting point $x_0$,
--   $$f_\mu(x)=f(x)+\frac\mu2\|x-x_0\|_0^2,\qquad \|h\|_0^2=\sum_{i=1}^n\|h^{(i)}\|_{(i)}^2 .$$
--   When the block norms are Euclidean, $\|h^{(i)}\|^2_{(i)}=\langle B_ih^{(i)},h^{(i)}\rangle$ with $B_i\succ0$ (3.4), $\|\cdot\|_0$ is the norm (3.9).
--
--   Strong convexity is the hypothesis of the linear-rate results (Theorem 2, the second bound of Theorem 5, Theorem 6). The function $f_\mu$ is the regularization behind Lemma 4 and the high-probability bound of Theorem 4; for convex $f$ and $\mu>0$ it is strongly convex in $\|\cdot\|_0$ with parameter $\mu$. (Theorem 3 uses the other regularization of p. 9, with $\|\cdot\|_1$ of (3.5) in place of $\|\cdot\|_0$; that one is not defined here.)
--
--   **Formalization Note** The paper calls $\sigma$ the convexity parameter and asks $\sigma>0$ in (3.1); here $\sigma$ is any real, and positivity (or $\sigma\ge0$, as Theorem 6 allows) is a hypothesis of each theorem that uses the notion. With $\sigma=0$ the condition is convexity of the differentiable $f$. $\langle\nabla f(x),y-x\rangle$ is the Fréchet derivative `fderiv ℝ f x (y - x)`. In `fReg`, $\|\cdot\|_0$ is the weighted norm of (2.7) for $\beta=0$; the weights $L_i^0=1$ make it independent of $L$. Block spaces $E_i$ are general real normed spaces here; the theorems that use (3.4) take them to be inner-product spaces, with $B_i$ absorbed into the inner product.
-- source:
--   Nesterov, Efficiency of coordinate descent methods on huge-scale optimization problems, CORE Discussion Paper 2010/2, p. 8, (3.1); p. 9, (3.4); p. 11, (3.9) and the regularized objective f_μ

import Mathlib
import Definitions.Def_NesterovRCD_Sublinear_Basic

namespace NesterovRCD.HighProb

open scoped BigOperators

variable {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]

/-- (3.1) in the norm ‖·‖_β with parameter σ: f differentiable and
f(y) ≥ f(x) + ⟨∇f(x), y − x⟩ + ½σ‖y − x‖²_β for all x, y (positivity of σ is a separate
hypothesis where the paper asks for it). -/
def StronglyConvexW (f : NesterovRCD.Sublinear.Blocks E → ℝ) (L : Fin n → ℝ) (β σ : ℝ) : Prop :=
  Differentiable ℝ f ∧ ∀ x y, f x + fderiv ℝ f x (y - x) + σ / 2 * NesterovRCD.Sublinear.wnorm L β (y - x) ^ 2 ≤ f y

/-- The regularized objective f_μ(x) = f(x) + (μ/2)‖x − x_0‖²_0 (p. 11), with ‖·‖_0 the norm
(2.7) for β = 0, i.e. ‖h‖²_0 = Σ_i ‖h^{(i)}‖²_{(i)}, which is (3.9) once the block norms are the
Euclidean norms (3.4). (`wnorm L 0` does not depend on L, since L_i^0 = 1.) -/
noncomputable def fReg (f : NesterovRCD.Sublinear.Blocks E → ℝ) (L : Fin n → ℝ) (μ : ℝ) (x0 : NesterovRCD.Sublinear.Blocks E) (x : NesterovRCD.Sublinear.Blocks E) : ℝ :=
  f x + μ / 2 * NesterovRCD.Sublinear.wnorm L 0 (x - x0) ^ 2

end NesterovRCD.HighProb


