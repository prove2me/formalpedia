-- Prove2me | Definitions.Def_LeanPool_DistanceGeometry_Defs
-- name    : LeanPool_DistanceGeometry_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:44:59.041087+00:00
-- url     : https://prove2.me/theorems/5b7e0749-b3f5-43d1-84af-de4e7021f771
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Egor Lyfar; LeanPool contributors's pinned Euclidean distance geometry development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/Defs.lean

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DistanceGeometry
open scoped RealInnerProductSpace
variable {n k : ℕ}
noncomputable def sqDistMatrix (x : Fin n → EuclideanSpace ℝ (Fin k)) :
    Matrix (Fin n) (Fin n) ℝ :=
  .of fun i j => dist (x i) (x j) ^ 2
def IsSqDistMatrix (D : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → EuclideanSpace ℝ (Fin k)) : Prop :=
  ∀ i j, D i j = dist (x i) (x j) ^ 2
def EmbedsIn (D : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) : Prop :=
  ∃ x : Fin n → EuclideanSpace ℝ (Fin k), IsSqDistMatrix D x
def IsPreDistMatrix (D : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, D i j = D j i) ∧ (∀ i, D i i = 0)
noncomputable def centeredGram [NeZero n] (D : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  .of fun i j => (D 0 i + D 0 j - D i j) / 2
end DistanceGeometry


