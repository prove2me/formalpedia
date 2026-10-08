-- Prove2me | Definitions.Def_IsometricImmersion
-- name    : IsometricImmersion
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:15.721173+00:00
-- url     : https://prove2.me/theorems/a2b57b85-055e-4c6e-acc0-8ed82fa1db32
-- statement:
--   This block sets up coordinates for local smooth surface geometry. Coord is the plane ℝ², realized as functions Fin 2 → ℝ, and Ambient is three-dimensional Euclidean space. The open square is the set of points of the plane whose two coordinates both lie strictly between -1 and 1, and a short lemma proves it is open by writing it as a finite intersection of preimages of the open interval (-1,1) under the continuous coordinate projections; this lets it be packaged as an open subset of Coord, called coordinateSquareOpen. LocalSmoothPositive is a defined predicate on a matrix-valued field g over an open set U of the plane, assigning a 2×2 real matrix to each point: it requires every matrix entry to be an infinitely differentiable function of the point, and every matrix g(p) to be positive definite, so g is a smooth Riemannian metric tensor on U in local coordinates.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/IsometricImmersion.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/IsometricImmersion.lean; bytes 253..1250
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

namespace OAI

noncomputable section
open Set TopologicalSpace
open scoped ContDiff Topology Manifold Matrix

namespace SmoothLocal.Geometry

abbrev Coord := Fin 2 → ℝ

abbrev Ambient := EuclideanSpace ℝ (Fin 3)

def square : Set Coord := {p | ∀ i, p i ∈ Set.Ioo (-1 : ℝ) 1}

def LocalSmoothPositive (U : Opens Coord)
    (g : U → Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  (∀ i j, ContMDiff 𝓘(ℝ, Coord) 𝓘(ℝ, ℝ) ∞ (fun p => g p i j)) ∧
    ∀ p, (g p).PosDef

end SmoothLocal.Geometry

namespace SmoothLocal.ODE
open SmoothLocal.Geometry

theorem coordinate_square_isOpen : IsOpen square := by
  have heq : square = ⋂ i : Fin 2,
      (fun p : Coord => p i) ⁻¹' Ioo (-1 : ℝ) 1 := by
    ext p
    simp [square]
  rw [heq]
  exact isOpen_iInter_of_finite (fun i => isOpen_Ioo.preimage (continuous_apply i))

end SmoothLocal.ODE

namespace SmoothLocal.Geometry

def coordinateSquareOpen : Opens Coord :=
  ⟨square, SmoothLocal.ODE.coordinate_square_isOpen⟩



end SmoothLocal.Geometry
end
end OAI


