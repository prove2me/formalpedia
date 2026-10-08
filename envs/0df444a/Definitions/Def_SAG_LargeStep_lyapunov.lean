-- Prove2me | Definitions.Def_SAG_LargeStep_lyapunov
-- name    : SAG_LargeStep_lyapunov
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T12:24:29.679864+00:00
-- url     : https://prove2.me/theorems/380a939f-45ff-48b7-bde7-e27e1dab55a9
-- title:
--   The Lyapunov function Q(θ) = 2g(x + (α/n)eᵀy) − 2g(x*) + (θ − θ*)ᵀ(A b; bᵀ c)(θ − θ*) of §A.6
-- statement:
--   For a SAG state $\theta=(y,x)$ write $\theta^*=(f_1'(x^*),\dots,f_n'(x^*),x^*)$, let $e=(I,\dots,I)^\top\in\mathbb R^{np\times p}$ so that $e^\top y=\sum_i y_i$, and fix parameters $\alpha,\eta,\nu$. The Lyapunov function of §A.6 is
--   $$Q(\theta)=2g\Big(x+\frac\alpha n e^\top y\Big)-2g(x^*)+(\theta-\theta^*)^\top\begin{pmatrix}A&b\\ b^\top&c\end{pmatrix}(\theta-\theta^*),$$
--   with $A=\frac{\eta\alpha}nI+\frac\alpha n(1-2\nu)ee^\top$, $b=-\nu e$ and $c=0$. Writing $u_i=y_i-f_i'(x^*)$, this is
--   $$Q(\theta)=2g\Big(x+\frac\alpha n\sum_i y_i\Big)-2g(x^*)+\frac{\eta\alpha}{n}\sum_i\|u_i\|^2+\frac\alpha n(1-2\nu)\Big\|\sum_i u_i\Big\|^2-2\nu\Big\langle\sum_i u_i,\,x-x^*\Big\rangle .$$
--
--   The proof of Proposition 2 uses $\eta=2$, $\nu=\frac1{2n}$ and $\alpha=\frac1{2n\mu}$.
--
--   **Formalization Note** `lyap f f' α η ν xstar θ` keeps $\alpha,\eta,\nu$ as parameters; the theorems instantiate them.
-- source:
--   Le Roux, Schmidt & Bach, A Stochastic Gradient Method with an Exponential Convergence Rate for Finite Training Sets, arXiv:1202.6258v4, pp. 23–24, §A.6 Step 1

import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum

namespace SAG.LargeStep

/-- The Lyapunov function of §A.6 (pp. 23–24) with parameters `α, η, ν`:
`Q(θ) = 2g(x + (α/n) eᵀy) − 2g(x*) + (θ − θ*)ᵀ (A b; bᵀ c) (θ − θ*)` with
`A = (ηα/n) I + (α/n)(1 − 2ν) eeᵀ`, `b = −νe`, `c = 0`, `θ = (y, x)`, `θ* = (f'(x*), x*)`.
Writing `uᵢ = yᵢ − f'ᵢ(x*)`, the quadratic part is
`(ηα/n) ∑ᵢ ‖uᵢ‖² + (α/n)(1 − 2ν) ‖∑ᵢ uᵢ‖² − 2ν ⟪∑ᵢ uᵢ, x − x*⟫`. -/
noncomputable def lyap {p n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (α η ν : ℝ)
    (xstar : EuclideanSpace ℝ (Fin p))
    (θ : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) : ℝ :=
  2 * SAGA.Convex.fAvg f (θ.2 + (α / (n : ℝ)) • ∑ i, θ.1 i) - 2 * SAGA.Convex.fAvg f xstar
    + η * α / (n : ℝ) * ∑ i, ‖θ.1 i - f' i xstar‖ ^ 2
    + α / (n : ℝ) * (1 - 2 * ν) * ‖∑ i, (θ.1 i - f' i xstar)‖ ^ 2
    - 2 * ν * inner ℝ (∑ i, (θ.1 i - f' i xstar)) (θ.2 - xstar)

end SAG.LargeStep


