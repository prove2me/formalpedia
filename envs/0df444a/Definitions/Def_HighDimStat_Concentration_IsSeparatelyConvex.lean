-- Prove2me | Definitions.Def_HighDimStat_Concentration_IsSeparatelyConvex
-- name    : HighDimStat_Concentration_IsSeparatelyConvex
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:23:34.389686+00:00
-- url     : https://prove2.me/theorems/b443f7a9-f6fc-41cc-ae46-40ce4d3fa5fd
-- title:
--   A separately convex function
-- statement:
--   A function $f:\mathbb R^n\to\mathbb R$ is **separately convex** if, for each index $k$, the
--   univariate function $y_k\mapsto f(x_1,\dots,x_{k-1},y_k,x_{k+1},\dots,x_n)$ is convex for
--   each fixed vector of the other coordinates. Strictly weaker than joint convexity of $f$
--   itself (Theorem 3.24's hypothesis, out of this mission's scope).
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 62 (PDF p. 82)

import Mathlib

namespace HighDimStat.Concentration

/-- **Separate convexity**, Wainwright, *High-Dimensional Statistics* (2019), p. 62. A function
`f : ℝⁿ → ℝ` is separately convex if, for each index `k`, the univariate function
`yₖ ↦ f(x₁,...,x_{k-1}, yₖ, x_{k+1},...,xₙ)` is convex for each fixed vector of the other
coordinates. Strictly weaker than joint convexity of `f` itself (Theorem 3.24's hypothesis, not
formalized in this mission). -/
def IsSeparatelyConvex {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ k : Fin n, ∀ x : Fin n → ℝ, ConvexOn ℝ Set.univ (fun yk => f (Function.update x k yk))

end HighDimStat.Concentration


