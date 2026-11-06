-- Prove2me | Definitions.Def_RollingProbeQN_Convex_IsAHPERun
-- name    : RollingProbeQN_Convex_IsAHPERun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:20:34.749892+00:00
-- url     : https://prove2.me/theorems/962fe9f5-8d3d-42d7-9275-234b1479870f
-- title:
--   Run of the accelerated hybrid proximal extragradient (A-HPE) recursion up to horizon $N$
-- statement:
--   Sequences $(\lambda_k,x_k,y_k,z_k,A_k)$ form an **A-HPE run** for a function $F$ and $\sigma$ up to horizon $N$ if $A_0=0$, $x_0=z_0$ and, for every $k<N$, $\lambda_k>0$,
--
--   $$a_k=\frac{\lambda_k+\sqrt{\lambda_k^2+4\lambda_kA_k}}{2},\quad A_{k+1}=A_k+a_k,\quad y_k=\frac{A_kx_k+a_kz_k}{A_{k+1}},$$
--
--   the relative proximal condition
--
--   $$\|x_{k+1}-y_k+\lambda_k\nabla F(x_{k+1})\|\le\sigma\|x_{k+1}-y_k\|,$$
--
--   and $z_{k+1}=z_k-a_k\nabla F(x_{k+1})$. This is the recursion of Monteiro and Svaiter on which Algorithm 1 is built; Appendix D proves its guarantees for convex differentiable $F$.
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, (1)–(2), pp. 7–8; Appendix D.1, p. 37

import Mathlib
import Definitions.Def_RollingProbeQN_Convex_aOf
import Definitions.Def_RollingProbeQN_Convex_yOf

namespace RollingProbeQN.Convex

/-- **A run of the accelerated hybrid proximal extragradient recursion, up to horizon `N`.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, §2.1, (1)–(2), pp. 7–8, and Appendix D.1, p. 37: "Initialize `A0 = 0` and `x0 = z0`. Given a
positive stepsize `λ_k`, set `a_k = (λ_k + √(λ_k² + 4λ_kA_k))/2`, `A_{k+1} = A_k + a_k`,
`y_k = (A_k x_k + a_k z_k)/A_{k+1}` […]; compute `x_{k+1}` by any procedure that satisfies the
relative proximal condition `‖x_{k+1} − y_k + λ_k ∇f(x_{k+1})‖ ≤ σ‖x_{k+1} − y_k‖` […] and set
`z_{k+1} = z_k − a_k ∇f(x_{k+1})`." Appendix D.1 uses it with a convex differentiable `F` in place of
`f`.

`IsAHPERun F σ N λ x y z A` says that the sequences satisfy the recursion and the relative condition
(2) at every step `k < N`. -/
def IsAHPERun {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℝ) (σ : ℝ) (N : ℕ) (lam : ℕ → ℝ)
    (x y z : ℕ → EuclideanSpace ℝ (Fin d)) (A : ℕ → ℝ) : Prop :=
  A 0 = 0 ∧ x 0 = z 0 ∧
  ∀ k < N, 0 < lam k ∧ A (k + 1) = A k + aOf (A k) (lam k) ∧ y k = yOf (A k) (x k) (z k) (lam k) ∧
    ‖x (k + 1) - y k + lam k • gradient F (x (k + 1))‖ ≤ σ * ‖x (k + 1) - y k‖ ∧
    z (k + 1) = z k - aOf (A k) (lam k) • gradient F (x (k + 1))

end RollingProbeQN.Convex


