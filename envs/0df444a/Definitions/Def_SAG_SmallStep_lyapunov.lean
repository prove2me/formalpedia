-- Prove2me | Definitions.Def_SAG_SmallStep_lyapunov
-- name    : SAG_SmallStep_lyapunov
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T12:25:58.471362+00:00
-- url     : https://prove2.me/theorems/ed536b78-9a2a-48c7-b4dc-b2a466691c86
-- title:
--   The quadratic Lyapunov function $Q(\theta)=(\theta-\theta^*)^\top P(\theta-\theta^*)$ of §A.5
-- statement:
--   Let $f'_1,\dots,f'_n:\mathbb R^p\to\mathbb R^p$ be the component gradients, $x^*\in\mathbb R^p$ and $\alpha\in\mathbb R$. Put $\theta^*=(f'_1(x^*),\dots,f'_n(x^*),x^*)$. The Lyapunov function of the analysis for the step size $\alpha=1/(2nL)$ is, for a SAG state $\theta=(y,x)$,
--   $$
--   Q(\theta)=(\theta-\theta^*)^\top\begin{pmatrix}A&b\\ b^\top&c\end{pmatrix}(\theta-\theta^*),
--   $$
--   $$
--   A=3n\alpha^2I+\frac{\alpha^2}{n}\Big(\frac1n-2\Big)ee^\top,\qquad b=-\alpha\Big(1-\frac1n\Big)e,\qquad c=I,
--   $$
--   with $e=(I;\dots;I)\in\mathbb R^{np\times p}$. Writing $u_i=y_i-f'_i(x^*)$, this is
--   $$
--   Q(y,x)=3n\alpha^2\sum_{i=1}^n\|u_i\|^2+\frac{\alpha^2}{n}\Big(\frac1n-2\Big)\Big\|\sum_{i=1}^n u_i\Big\|^2-2\alpha\Big(1-\frac1n\Big)\Big\langle\sum_{i=1}^n u_i,\,x-x^*\Big\rangle+\|x-x^*\|^2 .
--   $$
--
--   The proof of Proposition 1 shows that $Q$ contracts in expectation by the factor $1-\mu/(8nL)$ per step and dominates $\frac13\|x-x^*\|^2$.
--
--   **Formalization Note** $Q$ is defined through the block quadratic form of `SAG.SmallStep.blockForm`, with blocks $A_{ij}=[i=j]\,3n\alpha^2I+\frac{\alpha^2}{n}(\frac1n-2)I$, $b_i=-\alpha(1-\frac1n)I$, $c=I$; the step size, the gradients and $x^*$ are parameters.
-- source:
--   Le Roux, Schmidt & Bach, A Stochastic Gradient Method with an Exponential Convergence Rate for Finite Training Sets, arXiv:1202.6258v4, p. 19, §A.5 Step 1; p. 13 (θ*, e)

import Mathlib
import Definitions.Def_SAG_SmallStep_blockForm

namespace SAG.SmallStep

/-- The block `A = 3nα² I + (α²/n)(1/n − 2) e eᵀ` of the Lyapunov function (p. 19);
blockwise `A i j = [i = j] 3nα² I + (α²/n)(1/n − 2) I`. -/
noncomputable def lyapA {p n : ℕ} (α : ℝ) :
    Fin n → Fin n → (EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)) :=
  fun i j =>
    (if i = j then (3 * (n : ℝ) * α ^ 2) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin p))
      else 0)
    + (α ^ 2 / (n : ℝ) * (1 / (n : ℝ) - 2)) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin p))

/-- The block `b = −α(1 − 1/n) e` of the Lyapunov function (p. 19); every block is
`−α(1 − 1/n) I`. -/
noncomputable def lyapB {p n : ℕ} (α : ℝ) :
    Fin n → (EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)) :=
  fun _ => (-(α * (1 - 1 / (n : ℝ)))) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin p))

/-- The Lyapunov function of §A.5 (p. 19): `Q(θ) = (θ − θ*)ᵀ (A b; bᵀ c) (θ − θ*)` with
`A = lyapA α`, `b = lyapB α`, `c = I` and `θ* = (f'₁(x*), …, f'ₙ(x*), x*)`. -/
noncomputable def lyapunov {p n : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (α : ℝ)
    (xstar : EuclideanSpace ℝ (Fin p))
    (θ : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) : ℝ :=
  quadForm (lyapA α) (lyapB α) (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin p)))
    (fun i => θ.1 i - f' i xstar) (θ.2 - xstar)

end SAG.SmallStep


