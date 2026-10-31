-- Prove2me | Definitions.Def_SDEConvexOpt_argminSet
-- name    : SDEConvexOpt_argminSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:24:56.813597+00:00
-- url     : https://prove2.me/theorems/65434110-88d0-48ef-aa6b-a34af8f15d27
-- title:
--   The solution set $\mathcal S=\operatorname{argmin} f$
-- statement:
--   For $f:E\to\mathbb R$, the set of global minimizers
--   $$
--   \operatorname{argmin} f=\{x\in E:\ f(x)\le f(y)\ \text{for all } y\in E\}.
--   $$
--   For the objective of problem (P) it is the solution set $\mathcal S$; it may be empty in general, and the standing assumption (H0) requires it to be nonempty.
-- source:
--   Maulen S., Fadili, Attouch, An SDE perspective on stochastic convex optimization, arXiv:2207.02750v1, (P) and (H0), p.1

import Mathlib

open scoped NNReal

namespace SDEConvexOpt

/-- The solution set `S = argmin(f)` of the minimization problem (P)
(Maulen S., Fadili, Attouch, arXiv:2207.02750v1, (P) and (H0), p.1): the points where `f`
attains its global minimum over the whole space.

**Formalization Note** `argminSet f = {x | ∀ y, f x ≤ f y}`; it may be empty in general, and (H0)
assumes it is not. -/
def argminSet {E : Type*} (f : E → ℝ) : Set E := {x | ∀ y, f x ≤ f y}

end SDEConvexOpt


