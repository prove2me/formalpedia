-- Prove2me | Definitions.Def_HessianDamping_IGAHDSC_Setting
-- name    : HessianDamping_IGAHDSC_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T22:05:00.275592+00:00
-- url     : https://prove2.me/theorems/0116b08e-85ec-4a73-95c5-3896476a57d1
-- title:
--   Definition 1 and (IGAHD-SC): strong convexity, inertial run, rates, and energy
-- statement:
--   Let $H$ be a real Hilbert space and $f:H\to\mathbb R$. This file fixes the objects used in Theorem 11.
--
--   1. For $\mu>0$, $f$ is **$\mu$-strongly convex** when $z\mapsto f(z)-\frac{\mu}{2}\|z\|^2$ is convex.
--   2. For parameters $\mu,\beta,s$, a sequence $(x_k)$ is an **IGAHD-SC run** when, for every $k\ge1$ and $r=\sqrt{\mu s}$,
--   $$x_{k+1}=x_k+\frac{1-r}{1+r}(x_k-x_{k-1})-\frac{\beta\sqrt s}{1+r}(\nabla f(x_k)-\nabla f(x_{k-1}))-\frac{s}{1+r}\nabla f(x_k).$$
--   3. The rate constants are $q=(1+\frac12\sqrt{\mu s})^{-1}$ and $\theta=(1+\sqrt{\mu s})^{-1}$. For a minimizer $x^*$, the proof's auxiliary vector and energy are
--   $$v_k=\sqrt\mu(x_{k-1}-x^*)+\frac{x_k-x_{k-1}}{\sqrt s}+\beta\nabla f(x_{k-1}),\qquad E_k=f(x_k)-f(x^*)+\frac12\|v_k\|^2.$$
--
--   The run, vector, and energy give a shared notation for the convergence milestones. **Formalization Note** The recurrence and energy claims are used only for $k\ge1$; $x_0,x_1$ are unrestricted. Positivity of parameters is supplied by the theorems that use these definitions.
-- source:
--   Attouch, Chbani, Fadili, Riahi, First-order optimization algorithms via inertial systems with Hessian driven damping, arXiv:1907.10536v2, p. 19, Definition 1; p. 28, (25) and (IGAHD-SC); pp. 29–30, Theorem 11 and proof

import Mathlib
import Definitions.Def_HessianDamping_DINSC_Setting
import Definitions.Def_HessianDamping_IPAHDSC_Setting

namespace HessianDamping.IGAHDSC

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The explicit inertial gradient algorithm with Hessian damping (IGAHD-SC), p. 28.
The initial points `x 0` and `x 1` are free. -/
noncomputable def IsIGAHDSCRun (f : H → ℝ) (μ β s : ℝ) (x : ℕ → H) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    let r := Real.sqrt (μ * s)
    x (k + 1) = x k + ((1 - r) / (1 + r)) • (x k - x (k - 1)) -
      (β * Real.sqrt s / (1 + r)) •
        (gradient f (x k) - gradient f (x (k - 1))) -
      (s / (1 + r)) • gradient f (x k)

/-- The auxiliary vector in the proof of Theorem 11, p. 30, for `k ≥ 1`. -/
noncomputable def vK (f : H → ℝ) (μ β s : ℝ) (x : ℕ → H) (xstar : H)
    (k : ℕ) : H :=
  Real.sqrt μ • (x (k - 1) - xstar) +
    (1 / Real.sqrt s) • (x k - x (k - 1)) +
    β • gradient f (x (k - 1))

/-- The energy in the proof of Theorem 11, p. 30, for `k ≥ 1`. -/
noncomputable def EK (f : H → ℝ) (μ β s : ℝ) (x : ℕ → H) (xstar : H)
    (k : ℕ) : ℝ :=
  f (x k) - f xstar + (1 / 2) * ‖vK f μ β s x xstar k‖ ^ 2

end HessianDamping.IGAHDSC


