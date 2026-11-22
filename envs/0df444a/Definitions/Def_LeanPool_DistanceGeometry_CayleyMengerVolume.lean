-- Prove2me | Definitions.Def_LeanPool_DistanceGeometry_CayleyMengerVolume
-- name    : LeanPool_DistanceGeometry_CayleyMengerVolume
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:45:42.884264+00:00
-- url     : https://prove2.me/theorems/3da191a8-fa61-49fe-8b1c-431a02a8e8ca
-- title:
--   Cayley Menger Volume
-- statement:
--   Definitions and structural lemmas for Cayley Menger Volume, from Egor Lyfar; LeanPool contributors's pinned Euclidean distance geometry development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/CayleyMengerVolume.lean

module
public import Definitions.Def_LeanPool_DistanceGeometry_Defs
public import Definitions.Def_LeanPool_DistanceGeometry_Schoenberg
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DistanceGeometry
open Matrix
open scoped RealInnerProductSpace
variable {n : ℕ}
def cayleyMenger (D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
  Matrix.of (Fin.cons (Fin.cons 0 (fun _ => 1)) (fun i => Fin.cons 1 (D i)))
noncomputable def triangleArea (x : Fin 3 → EuclideanSpace ℝ (Fin 2)) : ℝ :=
  |((x 1 - x 0) 0 * (x 2 - x 0) 1 - (x 1 - x 0) 1 * (x 2 - x 0) 0)| / 2
end DistanceGeometry


