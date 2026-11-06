-- Prove2me | Definitions.Def_RollingProbeQN_Convex_epsReturns
-- name    : RollingProbeQN_Convex_epsReturns
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:27:11.617065+00:00
-- url     : https://prove2.me/theorems/f125def8-b82a-42f8-9d98-fe3eac48960e
-- title:
--   Iteration $k$ returns, for target accuracy $\varepsilon$
-- statement:
--   For a target accuracy $\varepsilon>0$, iteration $k$ of Algorithm 1 **returns** when the run has not returned before it and either $\nabla f(x_k)=0$ (Step 1) or the iteration completes with
--
--   $$A_{k+1}\ \ge\ \frac{R^2}{2\varepsilon}\qquad\text{(Step 5).}$$
--
--   The $\varepsilon$-run of Algorithm 1 is the run stopped at its first return.
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Algorithm 1, Steps 1 and 5, p. 9

import Mathlib
import Definitions.Def_RollingProbeQN_Convex_run

namespace RollingProbeQN.Convex

/-- **Iteration `k` returns, for target accuracy `ε`.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Algorithm 1, p. 9: "1. […] If `∇f(x_k) = 0`, return `x_k`. […] 5. Check progress. For target
accuracy `ε`, return `x_{k+1}` once `A_{k+1} ≥ R²/(2ε)`."

Iteration `k` returns when the run has not returned before it and either the oracle answer at `x_k` is
zero (Step 1) or the iteration completes with `A_{k+1} ≥ R²/(2ε)` (Step 5).

**Formalization Note.** The ε-run of Algorithm 1 is the run of `run` stopped at the first `k` with
`epsReturns`; the two coincide up to that iteration, since Step 5 only stops. -/
def epsReturns {d χ : ℕ} (cfg : Config d χ)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (x₀ : EuclideanSpace ℝ (Fin d))
    (R ε : ℝ) (k : ℕ) : Prop :=
  (run cfg G x₀ k).done = false ∧
    ((run cfg G x₀ k).gx = 0 ∨ R ^ 2 / (2 * ε) ≤ (run cfg G x₀ (k + 1)).A)

end RollingProbeQN.Convex


