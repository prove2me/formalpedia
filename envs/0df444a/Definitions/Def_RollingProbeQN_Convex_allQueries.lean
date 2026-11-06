-- Prove2me | Definitions.Def_RollingProbeQN_Convex_allQueries
-- name    : RollingProbeQN_Convex_allQueries
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:29:44.308857+00:00
-- url     : https://prove2.me/theorems/6746ff18-3ffa-4ff8-bbb1-55355603b676
-- title:
--   All oracle queries before iteration $k$
-- statement:
--   The list of all points at which the run calls the gradient oracle before iteration $k$ starts: the initial query $x_0$ followed by the queries of iterations $0,\dots,k-1$. Its length is the gradient count.
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Appendix E.4, p. 52

import Mathlib
import Definitions.Def_RollingProbeQN_Convex_iterQueries

namespace RollingProbeQN.Convex

/-- **All oracle queries before iteration `k`.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Appendix E.4, p. 52: "Initialization computes `∇f(x0)`. Iteration `k` computes […]".

`allQueries cfg G x₀ k = [x₀] ++ iterQueries 0 ++ ⋯ ++ iterQueries (k − 1)`: every point at which the
run calls the oracle before iteration `k` starts.

**Formalization Note.** Reading R4: the count includes the initial query at `x₀`. -/
noncomputable def allQueries {d χ : ℕ} (cfg : Config d χ)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (x₀ : EuclideanSpace ℝ (Fin d))
    (k : ℕ) : List (EuclideanSpace ℝ (Fin d)) :=
  x₀ :: (List.range k).flatMap (fun j => iterQueries cfg G x₀ j)

end RollingProbeQN.Convex


