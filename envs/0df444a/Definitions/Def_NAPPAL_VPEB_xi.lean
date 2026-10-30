-- Prove2me | Definitions.Def_NAPPAL_VPEB_xi
-- name    : NAPPAL_VPEB_xi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:13:41.427977+00:00
-- url     : https://prove2.me/theorems/57ef0548-7a5c-4df3-a26e-6c8f007992f2
-- title:
--   The subgradient $\xi = (\xi_u, \xi_v, \xi_p)$ of the proof of Proposition 3.1
-- statement:
--   For a sequence $w^k$ with step parameters $\epsilon^k$, define $\xi = (\xi_u, \xi_v, \xi_p)$ by
--   $$\begin{aligned}
--   \xi_u &= \nabla_u G(u^{k+1},v^{k+1}) - \nabla_u G(u^k,v^k) + (\nabla\Omega(u^{k+1}) - \nabla\Omega(u^k))^\top q^k + \nabla\Theta(u^{k+1})^\top (p^{k+1} - p^k) \\
--   &\quad + \gamma\,\nabla\Theta(u^{k+1})^\top\big[(\Theta(u^{k+1}) + Bv^{k+1}) - (\Theta(u^k) + Bv^k)\big] - \frac{1}{\epsilon^k}\big[\nabla K(u^{k+1}) - \nabla K(u^k)\big],\\
--   \xi_v &= \nabla_v G(u^{k+1},v^{k+1}) - \nabla_v G(u^k,v^k) + \nabla H(v^{k+1}) - \nabla H(v^k) + B^\top(p^{k+1} - p^k) \\
--   &\quad + \gamma B^\top\big[(\Theta(u^{k+1}) + Bv^{k+1}) - (\Theta(u^k) + Bv^k)\big] - \gamma B^\top B(v^{k+1} - v^k),\\
--   \xi_p &= \frac{1}{\gamma}(p^{k+1} - p^k).
--   \end{aligned}$$
--   The proof of Proposition 3.1 shows that $\xi$ is a subgradient of $\mathcal L_\gamma$ at $w^{k+1}$ whose norm is controlled by $\|w^k - w^{k+1}\|$.
--
--   **Formalization Note** $\nabla\Omega(u)^\top q$ is the adjoint of the Jacobian of $\Omega$ at $u$ applied to $q$, and likewise for $\Theta$.
-- source:
--   Zhu, Zhao, Zhang, A First-Order Primal-Dual Method for Nonconvex Constrained Optimization Based on the Augmented Lagrangian, arXiv:2007.12219v1, proof of Proposition 3.1, p. 10

import Mathlib
import Definitions.Def_NAPPAL_VPEB_W
import Definitions.Def_NAPPAL_VPEB_Problem
import Definitions.Def_NAPPAL_VPEB_Problem_Theta
import Definitions.Def_NAPPAL_VPEB_Params
import Definitions.Def_NAPPAL_VPEB_qk

namespace NAPPAL.VPEB

/-- **The vector `ξ = (ξ_u, ξ_v, ξ_p)` of the proof of Proposition 3.1.**
Zhu, Zhao, Zhang, *A First-Order Primal-Dual Method for Nonconvex Constrained Optimization
Based on the Augmented Lagrangian*, arXiv:2007.12219v1, proof of Proposition 3.1, p. 10: "Let us define
ξu = ∇uG(u^{k+1}, v^{k+1}) − ∇uG(u^k, v^k) + (∇Ω(u^{k+1}) − ∇Ω(u^k))⊤q^k + (∇Θ(u^{k+1}))⊤(p^{k+1} − p^k)
+ γ(∇Θ(u^{k+1}))⊤[(Θ(u^{k+1}) + Bv^{k+1}) − (Θ(u^k) + Bv^k)] − (1/ε^k)[∇K(u^{k+1}) − ∇K(u^k)],
ξv = ∇vG(u^{k+1}, v^{k+1}) − ∇vG(u^k, v^k) + ∇H(v^{k+1}) − ∇H(v^k) + B⊤(p^{k+1} − p^k)
+ γB⊤[(Θ(u^{k+1}) + Bv^{k+1}) − (Θ(u^k) + Bv^k)] − γB⊤B(v^{k+1} − v^k),
and ξp = (1/γ)(p^{k+1} − p^k)."

`xi P A w ε k` is the point `(ξ_u, ξ_v, ξ_p)` of `ℝⁿ × ℝᵈ × ℝᵐ` built from `w k`, `w (k+1)`,
`q^k` and `ε^k = ε k`.

**Formalization Note.** `(∇Ω(u))⊤q` is the adjoint of the Jacobian `fderiv ℝ P.Ω u` applied to
`q`, likewise for `Θ`; `B⊤` is `ContinuousLinearMap.adjoint P.B`. -/
noncomputable def xi {n d m : ℕ} (P : Problem n d m) (A : Params n) (w : ℕ → W n d m)
    (ε : ℕ → ℝ) (k : ℕ) : W n d m :=
  WithLp.toLp 2
    (WithLp.toLp 2
      ((gradient P.G (w (k + 1)).fst).fst - (gradient P.G (w k).fst).fst +
        ContinuousLinearMap.adjoint
          (fderiv ℝ P.Ω (w (k + 1)).fst.fst - fderiv ℝ P.Ω (w k).fst.fst) (qk P A w k) +
        ContinuousLinearMap.adjoint (fderiv ℝ P.Theta (w (k + 1)).fst.fst)
          ((w (k + 1)).snd - (w k).snd) +
        A.γ • ContinuousLinearMap.adjoint (fderiv ℝ P.Theta (w (k + 1)).fst.fst)
          ((P.Theta (w (k + 1)).fst.fst + P.B (w (k + 1)).fst.snd) -
            (P.Theta (w k).fst.fst + P.B (w k).fst.snd)) -
        (1 / ε k) • (gradient A.K (w (k + 1)).fst.fst - gradient A.K (w k).fst.fst),
      (gradient P.G (w (k + 1)).fst).snd - (gradient P.G (w k).fst).snd +
        gradient P.H (w (k + 1)).fst.snd - gradient P.H (w k).fst.snd +
        ContinuousLinearMap.adjoint P.B ((w (k + 1)).snd - (w k).snd) +
        A.γ • ContinuousLinearMap.adjoint P.B
          ((P.Theta (w (k + 1)).fst.fst + P.B (w (k + 1)).fst.snd) -
            (P.Theta (w k).fst.fst + P.B (w k).fst.snd)) -
        A.γ • ContinuousLinearMap.adjoint P.B (P.B ((w (k + 1)).fst.snd - (w k).fst.snd))),
    (1 / A.γ) • ((w (k + 1)).snd - (w k).snd))

end NAPPAL.VPEB


