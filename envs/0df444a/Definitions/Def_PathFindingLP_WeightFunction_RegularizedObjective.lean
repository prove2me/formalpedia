-- Prove2me | Definitions.Def_PathFindingLP_WeightFunction_RegularizedObjective
-- name    : PathFindingLP_WeightFunction_RegularizedObjective
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T22:46:11.754412+00:00
-- url     : https://prove2.me/theorems/fb95eb9c-4e99-4495-b163-27c64e0e7fba
-- title:
--   Regularized D-optimal-design objective $\hat f(s,w)$ (6) and Theorem 1's $\alpha,\beta$
-- statement:
--   Let $A\in\mathbb R^{m\times n}$, $s\in\mathbb R^m_{>0}$, $S=\mathrm{diag}(s)$ and $A_s=S^{-1}A$. For $w\in\mathbb R^m_{>0}$ let $W^\alpha=\mathrm{diag}(w_1^\alpha,\dots,w_m^\alpha)$. The objective (6) is
--
--   $$
--   \hat f(s,w)=\mathbb 1^\top w-\frac1\alpha\log\det\left(A_s^\top W^\alpha A_s\right)-\beta\sum_{i\in[m]}\log w_i ,
--   $$
--
--   and the weight function of the paper is $g(s)=\arg\min_{w\in\mathbb R^m_{>0}}\hat f(s,w)$. The predicate "$w$ is a regularized minimizer at $s$" says $w\in\mathbb R^m_{>0}$ and $\hat f(s,w)\le\hat f(s,w')$ for every $w'\in\mathbb R^m_{>0}$.
--
--   Theorem 1 of the paper fixes the constants
--
--   $$
--   \alpha = 1-\left(\log_2\frac{2m}{\mathrm{rank}(A)}\right)^{-1},\qquad \beta=\frac{\mathrm{rank}(A)}{2m}.
--   $$
--
--   At $\alpha=1$, $\beta=0$ the problem is the D-optimal design problem, dual to the John ellipsoid of the polytope $\{y:|[A(y-x)]_i|\le s_i\}$; the regularization by $\alpha<1$ and $\beta>0$ is what makes $g$ a well-behaved weight function.
--
--   **Formalization Note** $\log\det$ is `Real.log (Matrix.det …)` and $w_i^\alpha$ is `Real.rpow`; both are only meaningful for $w>0$ and full column rank of $A$ (otherwise `Real.log 0 = 0`), which is why the minimizer is taken over the positive orthant and every theorem assumes $\mathrm{rank}(A)=n$. $\log_2$ is `Real.logb 2`. The exponent $-1$ in $\alpha$ is read as the reciprocal of $\log_2\frac{2m}{\mathrm{rank}(A)}$, so that $\alpha\in(0,1)$ whenever $m>\mathrm{rank}(A)$.
-- source:
--   Lee, Sidford, Path Finding Methods for Linear Programming, FOCS 2014, pp. 424–433 (DOI 10.1109/FOCS.2014.52), p. 429, §V.A, eq. (6) and the constants α, β of Theorem 1 (Properties of Weight Function)

import Mathlib

namespace PathFindingLP.WeightFunction

open Matrix

/-- The objective (6) of Lee–Sidford 2014, §V.A, p. 429:
`f̂(s, w) = 𝟙ᵀ w − (1/α) log det(A_sᵀ W^α A_s) − β ∑ᵢ log wᵢ`, with `A_s = S⁻¹ A`,
`S = diag(s)` and `W^α = diag(wᵢ^α)`. -/
noncomputable def fhat {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (α β : ℝ) (s w : Fin m → ℝ) :
    ℝ :=
  ∑ i, w i
    - (1 / α) * Real.log (Matrix.det ((diagonal (fun i => (s i)⁻¹) * A)ᵀ *
        diagonal (fun i => w i ^ α) * (diagonal (fun i => (s i)⁻¹) * A)))
    - β * ∑ i, Real.log (w i)

/-- `w` is a minimizer of `f̂(s, ·)` over the open positive orthant `ℝ^m_{>0}`. -/
def IsRegularizedMinimizer {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (α β : ℝ)
    (s w : Fin m → ℝ) : Prop :=
  (∀ i, 0 < w i) ∧ ∀ w' : Fin m → ℝ, (∀ i, 0 < w' i) → fhat A α β s w ≤ fhat A α β s w'

/-- Theorem 1's exponent `α = 1 − (log₂(2m / rank A))⁻¹` (Lee–Sidford 2014, §V.A, p. 429). -/
noncomputable def thm1Alpha {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  1 - (Real.logb 2 (2 * (m : ℝ) / (A.rank : ℝ)))⁻¹

/-- Theorem 1's regularization weight `β = rank A / (2m)` (Lee–Sidford 2014, §V.A, p. 429). -/
noncomputable def thm1Beta {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  (A.rank : ℝ) / (2 * (m : ℝ))

end PathFindingLP.WeightFunction


