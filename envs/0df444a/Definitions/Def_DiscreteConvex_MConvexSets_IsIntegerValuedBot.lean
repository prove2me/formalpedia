-- Prove2me | Definitions.Def_DiscreteConvex_MConvexSets_IsIntegerValuedBot
-- name    : DiscreteConvex_MConvexSets_IsIntegerValuedBot
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:16:33.736667+00:00
-- url     : https://prove2.me/theorems/0e97b51b-8d33-462a-84df-f4f6989ccaf7
-- title:
--   Integer-valuedness of an R-cup-minus-infinity function
-- statement:
--   $\mu : 2^V \to \mathbb R \cup \{-\infty\}$ is **integer valued**: every finite value it takes is an integer. The supermodular-side counterpart of `IsIntegerValued`, used by Theorem 4.17.
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.111 (supporting Theorem 4.17)

import Mathlib

/-!
Integer-valuedness of an `R ∪ {-∞}`-valued set function, the supermodular-side counterpart used
by Theorem 4.17 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.111), in
`DiscreteConvex.MConvexSets`.
-/

namespace DiscreteConvex.MConvexSets

/-- `μ : 2ⱽ → R ∪ {-∞}` is **integer valued**: every finite value it takes is (the cast of) an
integer. -/
def IsIntegerValuedBot {V : Type*} (μ : Finset V → WithBot ℝ) : Prop :=
  ∀ X : Finset V, μ X = ⊥ ∨ ∃ k : ℤ, μ X = ((k : ℝ) : WithBot ℝ)

end DiscreteConvex.MConvexSets


