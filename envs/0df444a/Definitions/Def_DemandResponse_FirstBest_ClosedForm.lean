-- Prove2me | Definitions.Def_DemandResponse_FirstBest_ClosedForm
-- name    : DemandResponse_FirstBest_ClosedForm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T04:01:16.281354+00:00
-- url     : https://prove2.me/theorems/62b90a12-0f58-460d-aaf2-cf539cc171af
-- title:
--   The rates m̄ (p. 28) and m_FB (Prop. 3.1) and the functions v̄ of (A.6) and Prop. 3.1
-- statement:
--   This file defines the explicit functions appearing in the closed form of the first-best value. With $\delta=\kappa-\theta$ and $\rho=\frac{rp}{r+p}$,
--   $$\bar m(t):=H_m(\delta(T-t))+H_v\big(-h-\rho\delta^2(T-t)^2\big),\qquad \bar v(t,x):=\delta(T-t)x+\int_t^T\bar m(s)\,ds,$$
--   the solution of the first-best HJB equation (A.6) for linear $f-g$ (p. 28), and
--   $$m_{FB}(t):=\tfrac12\bar\mu(\delta^-)^2(T-t)^2+H_v\big(-h-\rho\delta^2(T-t)^2\big),\qquad \bar v_{FB}(t,x):=\delta(T-t)x+\int_t^Tm_{FB}(s)\,ds,$$
--   the function in the statement of Proposition 3.1 (i).
--
--   The first pair uses the Hamiltonian $H_m$ itself; the second uses its closed form $\frac12\bar\mu(\delta^-)^2(T-t)^2$, which coincides with $H_m(\delta(T-t))$ when $\delta^-(T-t)\le A_{\max}$.
--
--   **Formalization Note** On p. 28 the paper writes $\int_0^t\bar m(s)ds$; the terminal condition $\bar v(T,\cdot)=0$ of (A.6) and the statement of Proposition 3.1 both require $\int_t^T$, which is used here.
-- source:
--   arXiv:1810.09063v3, Proposition 3.1 (i) (p. 10) and Appendix A.2 (p. 28)

import Mathlib
import Definitions.Def_DemandResponse_FirstBest_Hamiltonian

namespace DemandResponse.FirstBest

variable {N d : ℕ}

/-- `m̄(t) := H_m(δ(T - t)) + H_v(-h - ρ δ² (T - t)²)` (p. 28), with the Hamiltonians defined by
their infima (2.9). -/
noncomputable def mbar (P : Params N d) (t : ℝ) : ℝ :=
  Hm P (delta P * (P.T - t)) + Hv P (-P.h - rho P * delta P ^ 2 * (P.T - t) ^ 2)

/-- `v̄(t, x) := δ(T - t) x + ∫ₜᵀ m̄(s) ds`, the solution of the first-best PDE (A.6) for
`(f - g)(x) = δ x` (p. 28, with the integral `∫ₜᵀ` forced by the terminal condition
`v̄(T, ·) = 0`). -/
noncomputable def vbarA6 (P : Params N d) (t x : ℝ) : ℝ :=
  delta P * (P.T - t) * x + ∫ s in t..P.T, mbar P s

/-- `m_FB(t) := ½ μ̄ (δ⁻)² (T - t)² + H_v(-h - ρ δ² (T - t)²)` (Prop. 3.1 (i)). -/
noncomputable def mFB (P : Params N d) (t : ℝ) : ℝ :=
  (1 / 2) * muBar P * xneg (delta P) ^ 2 * (P.T - t) ^ 2 +
    Hv P (-P.h - rho P * delta P ^ 2 * (P.T - t) ^ 2)

/-- `v̄(t, x) := δ(T - t) x + ∫ₜᵀ m_FB(s) ds` (Prop. 3.1 (i)). -/
noncomputable def vbarFB (P : Params N d) (t x : ℝ) : ℝ :=
  delta P * (P.T - t) * x + ∫ s in t..P.T, mFB P s

end DemandResponse.FirstBest


