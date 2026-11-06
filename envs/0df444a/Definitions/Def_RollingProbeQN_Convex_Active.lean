-- Prove2me | Definitions.Def_RollingProbeQN_Convex_Active
-- name    : RollingProbeQN_Convex_Active
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:26:52.64249+00:00
-- url     : https://prove2.me/theorems/1c8cc841-7fda-439b-8c6c-56f2d78b6cc6
-- title:
--   Iteration $k$ of Algorithm 1 is executed
-- statement:
--   Iteration $k$ of Algorithm 1 is **executed** when the run has not returned before $k$ and $\nabla f(x_k)\neq0$, so that Step 1 does not return. A completed horizon $N$ in Appendix E is a run in which iterations $0,\dots,N-1$ are executed.
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Algorithm 1, Step 1, p. 9

import Mathlib
import Definitions.Def_RollingProbeQN_Convex_run

namespace RollingProbeQN.Convex

/-- **Iteration `k` of Algorithm 1 is executed.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Algorithm 1, Step 1, p. 9: "If `∇f(x_k) = 0`, return `x_k`."

Iteration `k` is executed when the run has not returned before it and the oracle answer at `x_k` is
nonzero, so Step 1 does not return. -/
def Active {d χ : ℕ} (cfg : Config d χ)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (x₀ : EuclideanSpace ℝ (Fin d))
    (k : ℕ) : Prop :=
  (run cfg G x₀ k).done = false ∧ (run cfg G x₀ k).gx ≠ 0

end RollingProbeQN.Convex


