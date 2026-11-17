-- Prove2me | Definitions.Def_LawLocalComp_Supplement_IsCoupling
-- name    : LawLocalComp_Supplement_IsCoupling
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:04:04.947391+00:00
-- url     : https://prove2.me/theorems/553c0479-2c7a-4583-b381-c5c1cf596ae1
-- title:
--   A coupling of two finite laws
-- statement:
--   Let $X$ and $Y$ be finite nonnegative laws. A **coupling** of $X$ and $Y$ is a finitely supported nonnegative weight $\pi$ on pairs $(x, y) \in \mathbb R^2$ with marginals $X$ and $Y$:
--   $$
--   \sum_{y} \pi(x, y) = P(X = x) \quad\text{for every } x, \qquad \sum_{x} \pi(x, y) = P(Y = y) \quad\text{for every } y.
--   $$
--   It is the joint law of an input/output pair $(X, Y)$ of a law-local map, used in §6.1 to define the forward shortfall and the forward condition $E[\hat Y \mid X] = (1 + \varepsilon/4) X$.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), §6.1, p.10 ("For an input/output coupling π")

import Mathlib
import Definitions.Def_LawLocalComp_Law

open Classical

namespace LawLocalComp

namespace Supplement

/-- **A coupling of two finite laws.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), §6.1, p.10 ("For an input/output coupling π put s_π = E(X − E_π[Y | X])_+").

`IsCoupling π X Y`: `π` is a finitely supported nonnegative weight on pairs `(x, y)` whose first
marginal is `X` and whose second marginal is `Y` (the same coupling shape as in the published
`IsCondMean`). -/
def IsCoupling (π : ℝ × ℝ →₀ ℝ) (X Y : Law) : Prop :=
  (∀ z, 0 ≤ π z) ∧ (∀ x : ℝ, ∑ z ∈ π.support with z.1 = x, π z = X.w x) ∧
    ∀ y : ℝ, ∑ z ∈ π.support with z.2 = y, π z = Y.w y

end Supplement

end LawLocalComp


