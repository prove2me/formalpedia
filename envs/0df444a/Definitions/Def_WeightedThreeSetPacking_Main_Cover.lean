-- Prove2me | Definitions.Def_WeightedThreeSetPacking_Main_Cover
-- name    : WeightedThreeSetPacking_Main_Cover
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:50:22.448717+00:00
-- url     : https://prove2.me/theorems/23fa1480-a618-413c-9867-accbcf3530be
-- title:
--   Finite sheet covers and center reassignment
-- statement:
--   A finite $M$-sheet cover preserves vertex weights and membership in $A,O$, has exactly $M>0$ preimages of each vertex, and is locally bijective on graph neighborhoods. This predicate does not require injectivity on a union of neighborhoods. Reassigning centers leaves the graph and weights unchanged.
--
--   It is the ordinary graph-cover interface needed for the projection theorem. Existence, high girth and preservation of bounded local optimality are proof obligations of the structural theorem, not assumed data in the algorithmic goal.
-- source:
--   Tong and Xu, arXiv:2610.10036v1, §3.1, pp. 7–8; Lemma 4.1, pp. 12–13; https://arxiv.org/abs/2610.10036v1

import Definitions.Def_WeightedThreeSetPacking_Main_Analysis

namespace WeightedThreeSetPacking.Main
noncomputable section
open Classical

variable {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Literal weight-preserving finite graph-cover predicate. Local bijectivity
is on graph neighborhoods, not on unions of several talon neighborhoods. -/
def SheetCover (D : Analysis V) (E : Analysis W) (p : W → V) (M : ℕ) : Prop :=
  0 < M ∧
  (∀ v, (Finset.univ.filter fun x => p x = v).card = M) ∧
  (∀ x, E.w x = D.w (p x)) ∧
  (∀ x, x ∈ E.A ↔ p x ∈ D.A) ∧
  (∀ x, x ∈ E.O ↔ p x ∈ D.O) ∧
  (∀ x, Set.BijOn p {y | E.graph.Adj x y} {v | D.graph.Adj (p x) v})

/-- Replacing only the center function does not alter a cover's graph or weights. -/
def withCenter (D : Analysis V) (pi : V → V) : Analysis V := {D with center := pi}

end
end WeightedThreeSetPacking.Main


