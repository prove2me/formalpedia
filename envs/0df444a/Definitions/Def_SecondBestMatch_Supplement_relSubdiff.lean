-- Prove2me | Definitions.Def_SecondBestMatch_Supplement_relSubdiff
-- name    : SecondBestMatch_Supplement_relSubdiff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:41:40.236511+00:00
-- url     : https://prove2.me/theorems/fff17546-03ae-4369-8b5f-de3a79746f9a
-- title:
--   Subdifferential relative to $[0,1]$
-- statement:
--   For a function $U$ on $[0,1]$ and a point $t$, the **subdifferential of $U$ relative to $[0,1]$** is
--
--   $$
--   \partial_I U(t):=\{\,s\in\mathbb R:\ U(z)\ge U(t)+s(z-t)\ \text{ for every } z\in[0,1]\,\}.
--   $$
--
--   At an endpoint of $[0,1]$ this is the one-sided relative subdifferential. It expresses the envelope (subgradient) relation between an agent's interim service and the agent's interim utility potential in Definition A.1.
--
--   **Formalization Note** $U$ is a function $\mathbb R\to\mathbb R$ and only its values on $[0,1]$ and at $t$ matter. The paper uses $\partial_I U$ for convex $U$; convexity is imposed where the set is used, not in this definition.
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea7cce1bbfc7757c56937ec4ac13847b6d0025758a63fa8d6a25314385), Appendix A.1, p.27

import Mathlib

open Set

namespace SecondBestMatch.Supplement

/-- The subdifferential of `U` **relative to the interval `[0, 1]`** at `t`
(Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Appendix A.1, p.27):
`∂_I U(t) := {s ∈ ℝ : U(z) ≥ U(t) + s (z − t) for every z ∈ [0, 1]}`.
At an endpoint this is the one-sided relative subdifferential.

**Formalization Note** `U` is a function `ℝ → ℝ`; only its values on `[0, 1]` (and at `t`)
enter. The paper uses `∂_I U(t)` for convex `U` and `t ∈ [0, 1]`; convexity is imposed where
the set is used (`IsFullPotentialFeasible`), not here. -/
def relSubdiff (U : ℝ → ℝ) (t : ℝ) : Set ℝ :=
  {s | ∀ z ∈ Icc (0 : ℝ) 1, U t + s * (z - t) ≤ U z}

end SecondBestMatch.Supplement


