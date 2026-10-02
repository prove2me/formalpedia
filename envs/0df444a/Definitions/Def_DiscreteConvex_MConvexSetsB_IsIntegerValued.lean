-- Prove2me | Definitions.Def_DiscreteConvex_MConvexSetsB_IsIntegerValued
-- name    : DiscreteConvex_MConvexSetsB_IsIntegerValued
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:26:23.664067+00:00
-- url     : https://prove2.me/theorems/d1a9f5c9-185d-44c1-b858-1f4fcc32f125
-- title:
--   IsIntegerValued
-- statement:
--   $\rho : 2^V \to \mathbb R \cup \{+\infty\}$ is **integer valued** (the book's $\rho \in S[\mathbb Z]$) if every finite value it takes is an integer.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, pp.107-116 (supporting several results).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, pp.107-116 (supporting several results)

import Mathlib

/-!
Integer-valuedness of an `R ∪ {+∞}`-valued set function (the book's `ρ ∈ S[Z]`), used
throughout this mission (Murota, *Discrete Convex Analysis*, SIAM 2003, pp.107-116), in
`DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- `ρ : 2ⱽ → R ∪ {+∞}` is **integer valued** (the book's `ρ ∈ S[Z]`, as opposed to `S[R]`) if
every finite value it takes is (the cast of) an integer. -/
def IsIntegerValued {V : Type*} (ρ : Finset V → WithTop ℝ) : Prop :=
  ∀ X : Finset V, ρ X = ⊤ ∨ ∃ k : ℤ, ρ X = ((k : ℝ) : WithTop ℝ)

end DiscreteConvex.MConvexSetsB


