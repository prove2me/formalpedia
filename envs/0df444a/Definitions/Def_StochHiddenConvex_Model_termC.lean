-- Prove2me | Definitions.Def_StochHiddenConvex_Model_termC
-- name    : StochHiddenConvex_Model_termC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:54:15.836854+00:00
-- url     : https://prove2.me/theorems/5e237975-f5b7-40d0-bd30-694e7c24ce9b
-- title:
--   The terms $A_t$, $B_t$, $C_t$ of the one-step inequality (23)
-- statement:
--   For an MSG run with $u^t=g(x^t)$, $u^*=g(x^*)$ and the paper's iteration index $t$, the proof of Theorem 3.2 splits the error into
--   $$A_t=\mathbb E\|u^t-u^*\|^2-\mathbb E\|u^{t+1}-u^*\|^2,\qquad B_t=\mathbb E\big[\|g(x^t-\gamma v_F(x^t))-g(x^t)\|^2\big],$$
--   $$C_t=2\,\mathbb E\,(u^t-u^*)^\top\big[g(x^t-\gamma v_F(x^t))-g(x^t)+\gamma\nabla G(u^t)\big].$$
--   The definition also names the point $x^t-\gamma v_F(x^t)$, the integrand of $C_t$, and the proposition that every expectation used at iteration $t$ (of $F(x^t)$, $G(u^t)$, $\|u^t-u^*\|^2$, $\|u^{t+1}-u^*\|^2$ and the integrands of $B_t$, $C_t$) exists.
--
--   **Formalization Note** Expectations are over the law of the run. $\nabla G(u^t)$ is the right side of (5) at $u^t$.
-- source:
--   X. Chen, N. He, Y. Hu, Z. Ye, Efficient Algorithms for A Class of Stochastic Hidden Convex Optimization and Its Applications in Network Revenue Management, arXiv:2205.01774v3, Eq. (23), p.38; Eq. (27), p.39

import Mathlib
import Definitions.Def_StochHiddenConvex_Model_iterate

open MeasureTheory

namespace StochHiddenConvex

namespace Model

variable {d : ℕ} (M : Model d) [IsProbabilityMeasure M.P]
  (Lphi lam γ : ℝ) (K T : ℕ) (x1 xstar : Vec d)

/-- The point `x^t − γ v_F(x^t)` at which the proof of Theorem 3.2 evaluates `g`
(Chen, He, Hu & Ye, arXiv:2205.01774v3, p.38), for the paper's iteration `t = n + 1`. -/
noncomputable def mirrorPt (n : Fin T) (w : Fin T → Noise d K) : Vec d :=
  M.iterate Lphi lam γ K T x1 n w - γ • M.vF Lphi lam K (M.iterate Lphi lam γ K T x1 n w) (w n)

/-- `A_t := 𝔼‖u^t − u*‖² − 𝔼‖u^{t+1} − u*‖²` of (23) (arXiv:2205.01774v3, p.38), with
`u^t = g(x^t)`, `u* = g(x*)`, for the paper's iteration `t = n + 1`. -/
noncomputable def termA (n : Fin T) : ℝ :=
  (∫ w, ‖M.g (M.iterate Lphi lam γ K T x1 n w) - M.g xstar‖ ^ 2 ∂(M.runMeasure K T)) -
    ∫ w, ‖M.g (M.iterate Lphi lam γ K T x1 (n + 1) w) - M.g xstar‖ ^ 2 ∂(M.runMeasure K T)

/-- `B_t := 𝔼[‖g(x^t − γ v_F(x^t)) − g(x^t)‖²]` of (23) (arXiv:2205.01774v3, p.38). -/
noncomputable def termB (n : Fin T) : ℝ :=
  ∫ w, ‖M.g (M.mirrorPt Lphi lam γ K T x1 n w) - M.g (M.iterate Lphi lam γ K T x1 n w)‖ ^ 2
    ∂(M.runMeasure K T)

/-- The integrand of `C_t` of (23):
`2 (u^t − u*)ᵀ [g(x^t − γ v_F(x^t)) − g(x^t) + γ ∇G(u^t)]`. -/
noncomputable def integrandC (n : Fin T) (w : Fin T → Noise d K) : ℝ :=
  2 * inner ℝ (M.g (M.iterate Lphi lam γ K T x1 n w) - M.g xstar)
    (M.g (M.mirrorPt Lphi lam γ K T x1 n w) - M.g (M.iterate Lphi lam γ K T x1 n w) +
      γ • M.gradG (M.g (M.iterate Lphi lam γ K T x1 n w)))

/-- `C_t := 2 𝔼(u^t − u*)ᵀ [g(x^t − γ v_F(x^t)) − g(x^t) + γ ∇G(u^t)]` of (23) and (27)
(arXiv:2205.01774v3, pp.38–39). -/
noncomputable def termC (n : Fin T) : ℝ :=
  ∫ w, M.integrandC Lphi lam γ K T x1 xstar n w ∂(M.runMeasure K T)

/-- Every expectation taken at iteration `t = n + 1` in (23)–(24) exists: the integrands
`F(x^t)`, `G(u^t)`, `‖u^t − u*‖²`, `‖u^{t+1} − u*‖²`, the integrand of `B_t` and that of `C_t` are
integrable under the law of the run. -/
def StepIntegrable (n : Fin T) : Prop :=
  Integrable (fun w => M.F (M.iterate Lphi lam γ K T x1 n w)) (M.runMeasure K T) ∧
  Integrable (fun w => M.G (M.g (M.iterate Lphi lam γ K T x1 n w))) (M.runMeasure K T) ∧
  Integrable (fun w => ‖M.g (M.iterate Lphi lam γ K T x1 n w) - M.g xstar‖ ^ 2)
    (M.runMeasure K T) ∧
  Integrable (fun w => ‖M.g (M.iterate Lphi lam γ K T x1 (n + 1) w) - M.g xstar‖ ^ 2)
    (M.runMeasure K T) ∧
  Integrable (fun w => ‖M.g (M.mirrorPt Lphi lam γ K T x1 n w) -
    M.g (M.iterate Lphi lam γ K T x1 n w)‖ ^ 2) (M.runMeasure K T) ∧
  Integrable (M.integrandC Lphi lam γ K T x1 xstar n) (M.runMeasure K T)

end Model

end StochHiddenConvex


