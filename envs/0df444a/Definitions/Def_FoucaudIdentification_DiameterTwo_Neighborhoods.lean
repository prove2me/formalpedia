-- Prove2me | Definitions.Def_FoucaudIdentification_DiameterTwo_Neighborhoods
-- name    : FoucaudIdentification_DiameterTwo_Neighborhoods
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-31T02:19:35.698279+00:00
-- url     : https://prove2.me/theorems/7e277b02-6f74-4caf-a3a3-7a44db54ef81
-- title:
--   Neighborhood domination and selected-vertex separation
-- statement:
--   Closed domination includes equality and adjacency. A vertex distinguishes two vertices when it dominates exactly one of them. Domination and separation on a specified vertex set require witnesses in the selected finite set; separation concerns every distinct pair. These relations impose no global nonemptiness or feasibility assumption.
-- source:
--   Foucaud et al., arXiv:1405.2424v3, pp. 1–2, neighborhood conventions. https://arxiv.org/abs/1405.2424v3

import Mathlib

namespace FoucaudIdentification.DiameterTwo

/-- Closed-neighborhood domination, including self-domination. -/
def ClosedDom {V : Type} (G : SimpleGraph V) (x v : V) : Prop := x = v ∨ G.Adj x v

/-- Separation by a single selected vertex. -/
def Distinguishes {V : Type} (R : V → V → Prop) (x u v : V) : Prop :=
  (R x u ∧ ¬ R x v) ∨ (R x v ∧ ¬ R x u)

/-- Domination of a set of vertices by a selected finite set. -/
def DominatesOn {V : Type} (R : V → V → Prop) (S : Finset V) (X : Set V) : Prop :=
  ∀ v ∈ X, ∃ x ∈ S, R x v

/-- Every distinct pair in X has a selected separating witness. -/
def SeparatesOn {V : Type} (R : V → V → V → Prop)
    (S : Finset V) (X : Set V) : Prop :=
  ∀ u ∈ X, ∀ v ∈ X, u ≠ v → ∃ x ∈ S, R x u v

end FoucaudIdentification.DiameterTwo


