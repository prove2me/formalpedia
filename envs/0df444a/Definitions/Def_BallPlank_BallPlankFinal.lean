-- Prove2me | Definitions.Def_BallPlank_BallPlankFinal
-- name    : BallPlank_BallPlankFinal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T17:42:34.875912+00:00
-- url     : https://prove2.me/theorems/ba31dabe-0a5d-450d-9af2-ea68b51f8e3a
-- title:
--   Ball Plank Final
-- statement:
--   Definitions and structural lemmas for Ball Plank Final, from Arseniy Akopyan and Alexander Polyanskii (akopjan/Palomar-Bang-Ball; see pinned Apache-2.0 LICENSE and README.md)'s pinned A Short Proof of Ball's Plank Theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/akopjan/Palomar-Bang-Ball/blob/e57a2d8d0129b2d7ce3ee45c2064f5080c8c65eb/BallPlank/BallPlankFinal.lean

module
public import Definitions.Def_BallPlank_ShiftedPlanks
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Set
open scoped BigOperators InnerProductSpace Pointwise
noncomputable section
namespace PlankProblem
section Planks
variable {n : ℕ}
local notation "Rn" => EuclideanSpace ℝ (Fin n)
structure Plank (n : ℕ) where
  normal : EuclideanSpace ℝ (Fin n)
  lower : ℝ
  upper : ℝ
  normal_is_unit : ‖normal‖ = 1
  lower_le_upper : lower ≤ upper
namespace Plank
def carrier (P : Plank n) : Set Rn :=
  {x | P.lower ≤ ⟪x, P.normal⟫_ℝ ∧
       ⟪x, P.normal⟫_ℝ ≤ P.upper}
def width (P : Plank n) : ℝ :=
  P.upper - P.lower
instance : CoeOut (Plank n) (Set Rn) :=
  ⟨carrier⟩
end Plank
def directionalWidth (K : Set Rn) (u : Rn) : ℝ :=
  sSup ((fun x ↦ ⟪x, u⟫_ℝ) '' K) -
  sInf ((fun x ↦ ⟪x, u⟫_ℝ) '' K)
def relativeWidth (K : Set Rn) (P : Plank n) : ℝ :=
  P.width / directionalWidth K P.normal
def IsConvexBody (K : Set Rn) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty
def IsCentrallySymmetric (K : Set Rn) : Prop :=
  ∃ c : Rn, ∀ x, x ∈ K ↔ (2 : ℝ) • c - x ∈ K
def BangPlankConjecture : Prop :=
  ∀ {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (_ : IsConvexBody K)
    (P : Fin m → Plank n) (_ : K ⊆ ⋃ i, (P i : Set _)),
    1 ≤ ∑ i, relativeWidth K (P i)
def homothet (t : Rn) (r : ℝ) (K : Set Rn) : Set Rn :=
  t +ᵥ r • K
end Planks
end PlankProblem
end


