-- Prove2me | Definitions.Def_ConsistentSubmodular_Randomized_Impossibility_HardScalar
-- name    : ConsistentSubmodular_Randomized_Impossibility_HardScalar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:07:21.72413+00:00
-- url     : https://prove2.me/theorems/a895311a-c582-4dd4-be41-2ef4cd3db95e
-- title:
--   Scalar quantities of the randomized hard instance linear program
-- statement:
--   For a real parameter $x$ (in the proof, $x=u_1$, the root in $(0,1)$ of $\Phi(x)=x^4+x^3-2x^2-3x+2$), the following scalar expressions are defined.
--
--   - `lpThird x` $=y=x^2(1+x)$, the weight of the third group (at $x=u_1$, $u_2=u_1^2(1+u_1)$).
--   - `lpMuOne x` $=\mu_1=y/x-y=x(1+x)(1-x)$.
--   - `lpMuTwo x` $=\mu_2=1-y/x=1-x(1+x)$.
--   - `lpNumerator x` $=N=1+x-y$.
--   - `lpDenominator x` $=1+x+y-xy-y^2/x$, written without division as
--   $$1+x+y-xy-x^3(1+x)^2,\qquad y=x^2(1+x).$$
--   - `lpError x` $=\mu_1x+2\mu_2y$, the weight of the corrections $k-1$ and $k-2$ in the optimum and of the recourse terms.
--
--   These are the coefficients of the convex combination of the three last times of the hard stream in the randomized impossibility (Theorem 1, Appendix A.2); the ratio built from the numerator and denominator is the bound $\xi^\star$ at $x=u_1$ and the error term controls the lower-order losses.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/Impossibility/HardScalar.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

noncomputable section

namespace ConsistentSubmodular.HardInstance

/-- The weight `y = x² (1 + x)` of the third group; `u₂ = u₁² (1 + u₁)`. -/
def lpThird (x : ℝ) : ℝ := x ^ 2 * (1 + x)

/-- `μ₁ = y/x - y`. -/
def lpMuOne (x : ℝ) : ℝ := x * (1 + x) * (1 - x)

/-- `μ₂ = 1 - y/x`. -/
def lpMuTwo (x : ℝ) : ℝ := 1 - x * (1 + x)

/-- The numerator `N = 1 + x - y`. -/
def lpNumerator (x : ℝ) : ℝ := 1 + x - lpThird x

/-- The denominator `1 + x + y - x y - y²/x`, with `y²/x = x³ (1 + x)²`. -/
def lpDenominator (x : ℝ) : ℝ := 1 + x + lpThird x - x * lpThird x - x ^ 3 * (1 + x) ^ 2

/-- The weight `μ₁ x + 2 μ₂ y` of the corrections `k - 1` and `k - 2` of the
optimum and of the recourse terms. -/
def lpError (x : ℝ) : ℝ := lpMuOne x * x + 2 * lpMuTwo x * lpThird x

end ConsistentSubmodular.HardInstance

end


