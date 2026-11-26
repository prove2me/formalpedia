-- Prove2me | Definitions.Def_Sqrt6KissingBound_Optimality
-- name    : Sqrt6KissingBound_Optimality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T06:09:09.812603+00:00
-- url     : https://prove2.me/theorems/931f34bd-aba1-50e9-8446-cd165732ece7
-- title:
--   Optimality
-- statement:
--   Definitions and structural lemmas for Optimality, from Sébastien Palcoux (sebastienpalcoux/sqrt6-kissing-bound; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned The universal square-root-of-six exponential base bound for Euclidean kissing numbers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/Optimality.lean

import Definitions.Def_Sqrt6KissingBound_KissingBound
import Definitions.Def_Sqrt6KissingBound_StandardGeometry
set_option autoImplicit true
namespace Sqrt6KissingBound
noncomputable section
abbrev s3_opt : ℝ := Real.sqrt 3
def planePoint (x y : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  standardCoordinates 1 (x, ![y])
def hexPoint : Fin 6 → EuclideanSpace ℝ (Fin 2) :=
  ![planePoint 1 0,
    planePoint (1 / 2) (s3_opt / 2),
    planePoint (-1 / 2) (s3_opt / 2),
    planePoint (-1) 0,
    planePoint (-1 / 2) (-s3_opt / 2),
    planePoint (1 / 2) (-s3_opt / 2)]
def regularHexagon : Finset (EuclideanSpace ℝ (Fin 2)) :=
  by
    classical
    exact Finset.univ.image hexPoint
def IsUniversalKissingBase (α : ℝ) : Prop :=
  0 ≤ α ∧ ∀ {n : ℕ}, 1 ≤ n →
    ∀ X : Finset (EuclideanSpace ℝ (Fin n)),
      IsKissingConfiguration X → (X.card : ℝ) ≤ α ^ n
end
end Sqrt6KissingBound


