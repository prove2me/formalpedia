-- Prove2me | Definitions.Def_RBMSensitivity_Data_V
-- name    : RBMSensitivity_Data_V
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:35:30.762314+00:00
-- url     : https://prove2.me/theorems/1109bc3f-42b8-4135-becc-c5ae65e514db
-- title:
--   The Lyapunov function $V^\alpha$
-- statement:
--   For $r_1,r_2\in(0,\infty)$, the function $V^\alpha:\mathbb X\to[0,\infty)$,
--   $$V^\alpha(x,y):=\exp\big(r_1M^\alpha(x)+r_2\|y\|_{B^\alpha}\big),\qquad\xi=(x,y)\in\mathbb X.$$
--
--   It combines the Lyapunov function of the RBM with the $B^\alpha$ norm of the derivative process.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, §7.2, (7.4), p.28

import Mathlib
import Definitions.Def_RBMSensitivity_Data_M
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- The Lyapunov function `V^α(x, y) := exp(r_1 M^α(x) + r_2 ‖y‖_{B^α})` of (7.4):
arXiv:1907.00472v2, p.28.

**Formalization Note.** `M^α` is finite on `G` under Assumption 3.4, so `toReal` loses nothing. -/
noncomputable def Data.V {J : ℕ} (D : Data J) (B : ℝ → Set (E J)) (r₁ r₂ α : ℝ)
    (ξ : E J × E J) : ℝ :=
  Real.exp (r₁ * (D.M α ξ.1).toReal + r₂ * gauge (B α) ξ.2)

end RBMSensitivity


