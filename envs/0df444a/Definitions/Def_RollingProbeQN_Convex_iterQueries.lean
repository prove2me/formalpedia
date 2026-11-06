-- Prove2me | Definitions.Def_RollingProbeQN_Convex_iterQueries
-- name    : RollingProbeQN_Convex_iterQueries
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:27:42.943914+00:00
-- url     : https://prove2.me/theorems/f8277967-95e0-4110-a9c0-3f5c641a39d3
-- title:
--   The oracle queries of one iteration
-- statement:
--   The list of points at which iteration $k$ calls the gradient oracle: the probe point $x_k+\tau_kv_{g_{i_k}}$, the extrapolated point $y_k$ and the new iterate $x_{k+1}$ when the iteration is executed, and no point otherwise. The gradient at $x_k$ is cached from the previous iteration.
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Appendix E.4, p. 52

import Mathlib
import Definitions.Def_RollingProbeQN_Convex_iterAt
import Definitions.Def_RollingProbeQN_Convex_Active

namespace RollingProbeQN.Convex

/-- **The oracle queries of iteration `k`.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Appendix E.4, p. 52: "Iteration `k` computes the probe gradient `∇f(x_k + τ_k v_{g_{i_k}})` of
(4), the gradient `∇f(y_k)` for the model step, and `∇f(x_{k+1})` for the momentum update".

The list of points at which iteration `k` calls the oracle: empty when the iteration is not executed
(the run has returned, or Step 1 returns), and the probe point, `y_k` and `x_{k+1}` otherwise.

**Formalization Note.** Readings R3, R4: the gradient count is the number of oracle calls. -/
noncomputable def iterQueries {d χ : ℕ} (cfg : Config d χ)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (x₀ : EuclideanSpace ℝ (Fin d))
    (k : ℕ) : List (EuclideanSpace ℝ (Fin d)) :=
  open Classical in
  if Active cfg G x₀ k then
    [(iterAt cfg G x₀ k).probe, (iterAt cfg G x₀ k).y, (iterAt cfg G x₀ k).x']
  else []

end RollingProbeQN.Convex


