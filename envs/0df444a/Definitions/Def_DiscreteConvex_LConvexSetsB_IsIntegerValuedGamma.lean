-- Prove2me | Definitions.Def_DiscreteConvex_LConvexSetsB_IsIntegerValuedGamma
-- name    : DiscreteConvex_LConvexSetsB_IsIntegerValuedGamma
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:41:39.653789+00:00
-- url     : https://prove2.me/theorems/ad39e06f-c14d-42fb-bd0e-146f4b15a362
-- title:
--   IsIntegerValuedGamma
-- statement:
--   $\gamma : V \times V \to \mathbb R \cup \{+\infty\}$ is **integer valued**.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, pp.122-124 (supporting several results).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, pp.122-124 (supporting several results)

import Mathlib

/-!
Integer-valuedness of a distance function (the book's `γ ∈ T[Z]` side condition),
supporting Propositions 5.1 and 5.4 (Murota, *Discrete Convex Analysis*, SIAM 2003,
pp.122-124), in `DiscreteConvex.LConvexSetsB`.
-/

namespace DiscreteConvex.LConvexSetsB

/-- `γ : V × V → R ∪ {+∞}` is **integer valued**. -/
def IsIntegerValuedGamma {V : Type*} (γ : V → V → WithTop ℝ) : Prop :=
  ∀ u v, γ u v = ⊤ ∨ ∃ k : ℤ, γ u v = ((k : ℝ) : WithTop ℝ)

end DiscreteConvex.LConvexSetsB


