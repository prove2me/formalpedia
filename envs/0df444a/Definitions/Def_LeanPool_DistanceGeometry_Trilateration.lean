-- Prove2me | Definitions.Def_LeanPool_DistanceGeometry_Trilateration
-- name    : LeanPool_DistanceGeometry_Trilateration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:45:00.148762+00:00
-- url     : https://prove2.me/theorems/20ffa910-77bb-4b91-862b-1ba43c0f339a
-- title:
--   Trilateration
-- statement:
--   Definitions and structural lemmas for Trilateration, from Egor Lyfar; LeanPool contributors's pinned Euclidean distance geometry development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/Trilateration.lean

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DistanceGeometry
open scoped RealInnerProductSpace
open EuclideanGeometry Module Submodule
section General
variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P] [FiniteDimensional ℝ V]
  {ι : Type*} {c : ι → P} {r : ι → ℝ}
def sphereIntersection (c : ι → P) (r : ι → ℝ) : Set P :=
  {p | ∀ i, dist p (c i) = r i}
end General
def trilaterationSet (c : Fin 3 → EuclideanSpace ℝ (Fin 3)) (r : Fin 3 → ℝ) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  {p : EuclideanSpace ℝ (Fin 3) | ∀ i, dist p (c i) = r i}
variable {c : Fin 3 → EuclideanSpace ℝ (Fin 3)}
end DistanceGeometry


