-- Prove2me | Definitions.Def_AnytimeAdaVR_dSeq
-- name    : AnytimeAdaVR_dSeq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:26:49.727195+00:00
-- url     : https://prove2.me/theorems/1575d544-fe85-42a3-928f-e409a5b44f56
-- title:
--   The noiseless path D (AdaGrad-Norm)
-- statement:
--   The D path starts at $x_0=x_{\mathrm{init}}$, $h_0=1$, and for $t=0,1,\dots$ uses a fresh sample $\xi_t$:
--   $$
--   u_t=g(x_t;\xi_t),\qquad h_{t+1}=\sqrt{h_t^2+\|u_t\|^2},\qquad x_{t+1}=x_t-\frac{u_t}{h_{t+1}} .
--   $$
--   Local query $t+1$ evaluates $u_t$.
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41…74006), §5.2, eq. (13), p.8; Algorithm 3, p.9; eq. (49), p.24

import Mathlib

namespace AnytimeAdaVR

/-- **The continuing noiseless path D.** Jiang–Wang–Yang–Zhang–Li, *Adaptive Variance Reduction across Smoothness and Noise Conditions*
(preprint, 2026), §5.2, p.8, eq. (13), and Algorithm 3, p.9:
"Initialize x_0 = xinit and h_0 = 1. For t = 0, 1, …, draw a fresh sample and set u_t = g(x_t; ξ_t),
h_{t+1} = √(h_t² + ‖u_t‖²), x_{t+1} = x_t − u_t/h_{t+1}."

`dSeq g xinit ξ t = (x_t, h_t)`; local query `t + 1` uses the sample `ξ t`. -/
noncomputable def dSeq {d : ℕ} {Ξ : Type*}
    (g : EuclideanSpace ℝ (Fin d) → Ξ → EuclideanSpace ℝ (Fin d))
    (xinit : EuclideanSpace ℝ (Fin d)) (ξ : ℕ → Ξ) : ℕ → EuclideanSpace ℝ (Fin d) × ℝ
  | 0 => (xinit, 1)
  | t + 1 =>
      let st := dSeq g xinit ξ t
      let u := g st.1 (ξ t)
      let h := Real.sqrt (st.2 ^ 2 + ‖u‖ ^ 2)
      (st.1 - h⁻¹ • u, h)

end AnytimeAdaVR


