-- Prove2me | Definitions.Def_GuoZhaoADRC_extState
-- name    : GuoZhaoADRC_extState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:39:40.090589+00:00
-- url     : https://prove2.me/theorems/1558b06e-aae2-4d2f-8571-360a945e00f0
-- title:
--   The extended state $x^i_{n_i+1}=f_i(x,\xi,w_i)+\sum_k(a_{ik}-b_{ik})u_k$
-- statement:
--   Along trajectories $x,\xi,\hat x$ of the closed loop, the **extended state** (total disturbance) of subsystem $i$ is
--
--   $$x^i_{n_i+1}(t)=f_i\bigl(x(t),\xi(t),w_i(t)\bigr)+\sum_{k=1}^m(a_{ik}-b_{ik})\,u_k(t).$$
--
--   It collects the unmodelled dynamics, the external disturbance and the control-gain mismatch. The last observer state $\hat x^i_{n_i+1}$ estimates it, and the case $j=n_i+1$ of Theorem 3.1 (3.4) bounds the estimation error. Its time derivative is the quantity $\bar\Delta_i$ of (3.7).
--
--   **Formalization Note** The gains $a_{ik}$ are constants (correction of GA2).
-- source:
--   B.-Z. Guo, Z.-L. Zhao, On convergence of the nonlinear active disturbance rejection control for MIMO systems, SIAM J. Control Optim. 51(2) (2013) 1727–1757, doi:10.1137/110856824, the sentence after (3.2), p.1737

import Mathlib
import Definitions.Def_GuoZhaoADRC_ADRCData
import Definitions.Def_GuoZhaoADRC_ctrl

namespace GuoZhaoADRC

/-- **The extended state (total disturbance)
`x^i_{n_i+1} = f_i(x, ξ, w_i) + ∑_k (a_ik − b_ik) u_k` along a trajectory.**
Guo–Zhao, SIAM J. Control Optim. 51 (2013), the sentence after (3.2), p.1737.

The ESO's last state `x̂^i_{n_i+1}` estimates this quantity, and Theorem 3.1 (3.4) with
`j = n_i + 1` compares the two. Its time derivative is the page's `Δ̄_i` (3.7).

**Formalization Note.** `a_ik` is constant (correction of GA2). `x`, `ξ`, `xhat` are arbitrary
trajectories here; along a closed-loop solution this is the page's `x^i_{n_i+1}(t)`. -/
noncomputable def extState {m : ℕ} {n : Fin m → ℕ} {s : ℕ} (D : ADRCData m n s)
    (x : ℝ → EuclideanSpace ℝ (Σ i : Fin m, Fin (n i))) (ξ : ℝ → EuclideanSpace ℝ (Fin s))
    (xhat : ℝ → (i : Fin m) → Fin (n i + 1) → ℝ) (i : Fin m) (t : ℝ) : ℝ :=
  D.f i (x t) (ξ t) (D.w t i) + ∑ k, (D.a i k - D.b i k) * ctrl D xhat k t

end GuoZhaoADRC


