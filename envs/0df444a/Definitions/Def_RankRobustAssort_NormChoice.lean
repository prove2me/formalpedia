-- Prove2me | Definitions.Def_RankRobustAssort_NormChoice
-- name    : RankRobustAssort_NormChoice
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:24:10.920605+00:00
-- url     : https://prove2.me/theorems/30e3eff0-2f4d-44dd-ae02-6c1e17abbc2d
-- title:
--   Error norm: $\ell_1$ or $\ell_\infty$
-- statement:
--   The robust model measures the estimation error with a norm $\|\cdot\|$ that is, by the paper's standing convention, **either the $\ell_1$-norm or the $\ell_\infty$-norm**. This definition is the two-valued choice between them; every problem instance carries one of the two, so a result stated for all instances holds for both norms.
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, Notation (end of §1), p.6

import Mathlib

namespace RankRobustAssort

/-- The norm `‖·‖` measuring the estimation error `ϵ` in the consistent set `𝒰`: either the
`ℓ₁`-norm or the `ℓ∞`-norm.

Sturt, *The value of robust assortment optimization under ranking-based choice models*,
arXiv:2112.05010v4, Notation (end of §1), p.6: "We assume throughout that a norm ∥·∥ is either
the ℓ1-norm or ℓ∞-norm".

Formalization Note: the choice is data of the problem instance (`Problem.norm`), so every result
stated for an arbitrary `Problem` holds for both norms. -/
inductive NormChoice where
  /-- the `ℓ₁`-norm -/
  | l1
  /-- the `ℓ∞`-norm -/
  | linf
  deriving DecidableEq

end RankRobustAssort


