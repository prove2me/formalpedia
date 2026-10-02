-- Prove2me | Definitions.Def_LeblSCV_Pseudoconvex_IsHolomorphicallyConvex
-- name    : LeblSCV_Pseudoconvex_IsHolomorphicallyConvex
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T04:49:07.046637+00:00
-- url     : https://prove2.me/theorems/8a51a54a-f4b2-4eef-b896-6cf308bf08ee
-- title:
--   Definition 2.6.1 — holomorphically convex domain
-- statement:
--   A domain $U \subset \mathbb{C}^n$ is **holomorphically convex** if
--   $$K \subset\subset U \implies \widehat{K}_U \subset\subset U.$$
--   In other words, $U$ is convex with respect to the moduli of holomorphic functions on $U$.
--
--   **Formalization Note.** Being a domain (`IsOpen U ∧ IsConnected U`) is part of the definition.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 98, Definition 2.6.1

import Mathlib
import Definitions.Def_LeblSCV_Pseudoconvex_holomorphicHull
import Definitions.Def_LeblSCV_Pseudoconvex_IsRelCompactIn

namespace LeblSCV.Pseudoconvex

/-- Definition 2.6.1, holomorphic convexity (Lebl, p. 98): a domain `U ⊂ ℂⁿ` is
*holomorphically convex* if whenever `K ⊂⊂ U`, then `K̂_U ⊂⊂ U`. -/
def IsHolomorphicallyConvex {n : ℕ} (U : Set (EuclideanSpace ℂ (Fin n))) : Prop :=
  IsOpen U ∧ IsConnected U ∧
    ∀ K : Set (EuclideanSpace ℂ (Fin n)), IsRelCompactIn K U →
      IsRelCompactIn (holomorphicHull U K) U

end LeblSCV.Pseudoconvex


