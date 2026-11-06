-- Prove2me | Definitions.Def_RollingProbeQN_Convex_epsOutput
-- name    : RollingProbeQN_Convex_epsOutput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:27:07.323271+00:00
-- url     : https://prove2.me/theorems/2c138ad1-38bc-49b4-91ee-3e3ab413d3ea
-- title:
--   The point returned by Algorithm 1
-- statement:
--   The point returned at iteration $k$: $x_k$ if $\nabla f(x_k)=0$ (Step 1), and $x_{k+1}$ otherwise (Step 5).
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Algorithm 1, Steps 1 and 5, p. 9

import Mathlib
import Definitions.Def_RollingProbeQN_Convex_run

namespace RollingProbeQN.Convex

/-- **The point returned at iteration `k`.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Algorithm 1, p. 9: Step 1 returns `x_k`; Step 5 returns `x_{k+1}`.

The point returned when iteration `k` returns: `x_k` if the oracle answer at `x_k` is zero, and
`x_{k+1}` otherwise. -/
noncomputable def epsOutput {d χ : ℕ} (cfg : Config d χ)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (x₀ : EuclideanSpace ℝ (Fin d))
    (k : ℕ) : EuclideanSpace ℝ (Fin d) :=
  open Classical in
  if (run cfg G x₀ k).gx = 0 then (run cfg G x₀ k).x else (run cfg G x₀ (k + 1)).x

end RollingProbeQN.Convex


