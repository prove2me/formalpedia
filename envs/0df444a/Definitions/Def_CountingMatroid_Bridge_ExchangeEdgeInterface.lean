-- Prove2me | Definitions.Def_CountingMatroid_Bridge_ExchangeEdgeInterface
-- name    : CountingMatroid_Bridge_ExchangeEdgeInterface
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T15:48:28.61228+00:00
-- url     : https://prove2.me/theorems/5328a086-a656-4364-ba01-40c43f73f0b8
-- title:
--   Directed exchange edge for matroid intersection
-- statement:
--   For matroids M₁ and M₂ on a finite ground set and a set I, a directed exchange edge u → v exists when either u is in I and v is outside I with (I − {u}) ∪ {v} independent in M₁, or u is outside I and v is in I with (I − {v}) ∪ {u} independent in M₂. This definition supplies the standard combinatorial predicate computed by the fixed oracle program.
-- source:
--   Mathlib matroid independence interface, with no Arlib dependency; added to the existing approximate common-bases mission.

import Definitions.Def_CommonBasesFPRAS

set_option autoImplicit false

namespace CountingMatroid.Bridge

open scoped Classical

/-- Directed exchange edge in the usual matroid-intersection graph: outside
elements point to inside elements when the first matroid permits exchange;
inside elements point to outside elements when the second does. -/
noncomputable def matroidExchangeEdge {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (I : Finset (Fin n)) (u v : Fin n) : Bool := decide
  ((u ∈ I ∧ v ∉ I ∧
      M₁.Indep (insert v ((I.erase u : Finset (Fin n)) : Set (Fin n)))) ∨
   (u ∉ I ∧ v ∈ I ∧
      M₂.Indep (insert u ((I.erase v : Finset (Fin n)) : Set (Fin n)))))

end CountingMatroid.Bridge


