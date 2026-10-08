-- Prove2me | Definitions.Def_SherbrookeMetric_ConvexHull_LowerHull
-- name    : SherbrookeMetric_ConvexHull_LowerHull
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:51:00.905968+00:00
-- url     : https://prove2.me/theorems/ac1b1e2c-229b-4a19-8c65-cb443ec6a14b
-- title:
--   Appendix — lower convex hull of an item function
-- statement:
--   For an item function $\Xi:\mathbb N\to\mathbb R$, its **lower convex hull** $H$ is the greatest discretely convex function lying at or below $\Xi$. At each stock level $m$ it is defined by
--
--   $$
--   H(m)=\sup\{g(m):g\text{ is discretely convex and }g(k)\le\Xi(k)\text{ for every }k\ge0\}.
--   $$
--
--   This gives the boundary function $\Xi'$ used by Sherbrooke's marginal conditions. When $\Xi$ has a finite lower bound, the family contains a constant function; because every member is at most $\Xi(m)$, the supremum is a finite real number.
--
--   **Formalization Note** The definition is a total real-valued Lean function. Its theorems require the paper's lower-bound condition, under which the real supremum has the stated meaning.
-- source:
--   Sherbrooke, METRIC: A Multi-Echelon Technique for Recoverable Item Control, Oper. Res. 16 (1968), pp. 135–136, Generalization of the Objective Function, and p. 140, Appendix THEOREM; DOI 10.1287/opre.16.1.122

import Mathlib
import Definitions.Def_SherbrookeMetric_ConvexHull_DiscreteConvex

namespace SherbrookeMetric.ConvexHull

/-- Appendix, p. 140, with the description on pp. 135–136: the lower convex
envelope of `Ξ` at each nonnegative integer. Under the paper's lower-bound
hypothesis the family is nonempty (it contains a constant minorant); at each
point it is bounded above by `Ξ` there. Thus the real supremum has its usual
mathematical meaning in every theorem in this mission. -/
noncomputable def lowerHull (Ξ : ℕ → ℝ) (m : ℕ) : ℝ :=
  ⨆ g : {g : ℕ → ℝ // DiscreteConvex g ∧ ∀ k : ℕ, g k ≤ Ξ k}, g.1 m

end SherbrookeMetric.ConvexHull


