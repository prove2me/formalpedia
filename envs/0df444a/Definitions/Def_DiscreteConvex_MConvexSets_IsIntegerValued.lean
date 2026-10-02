-- Prove2me | Definitions.Def_DiscreteConvex_MConvexSets_IsIntegerValued
-- name    : DiscreteConvex_MConvexSets_IsIntegerValued
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:16:28.555724+00:00
-- url     : https://prove2.me/theorems/40a803f3-c441-425c-bd83-604b005a0ce0
-- title:
--   Integer-valuedness of an R-cup-infinity function
-- statement:
--   $\rho : 2^V \to \mathbb R \cup \{+\infty\}$ is **integer valued** (the book's $\rho \in S[\mathbb Z]$) if every finite value it takes is an integer.
--
--   Supporting notion for the integrality clauses of Theorems 4.17 and 4.18.
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, pp.111-114 (supporting Theorems 4.17, 4.18)

import Mathlib

/-!
Integer-valuedness of an `R ∪ {+∞}`-valued set function, used for the integrality clauses of
Theorems 4.17 and 4.18 (Murota, *Discrete Convex Analysis*, SIAM 2003, pp.111-114), in
`DiscreteConvex.MConvexSets`.
-/

namespace DiscreteConvex.MConvexSets

/-- `ρ : 2ⱽ → R ∪ {+∞}` is **integer valued** (the book's `ρ ∈ S[Z]`, as opposed to `S[R]`) if
every finite value it takes is (the cast of) an integer. -/
def IsIntegerValued {V : Type*} (ρ : Finset V → WithTop ℝ) : Prop :=
  ∀ X : Finset V, ρ X = ⊤ ∨ ∃ k : ℤ, ρ X = ((k : ℝ) : WithTop ℝ)

end DiscreteConvex.MConvexSets


