-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaGraphPiece
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaGraphPiece
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:55:54.66735+00:00
-- url     : https://prove2.me/theorems/25907242-cc46-483b-8125-d6ae1bfca6fe
-- title:
--   PArea Graph Piece
-- statement:
--   Definitions and structural lemmas for PArea Graph Piece, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAreaGraphPiece.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaGraphPiece
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_VolumeLtHausdorffUnitBallTwenty
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MeasureTheory Module
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace AreaGraphPiece
variable {k m : ℕ}
def pairPt (u : EuclideanSpace ℝ (Fin k)) (w : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin k ⊕ Fin m) :=
  WithLp.toLp 2 (Sum.elim (fun i => u i) (fun i => w i))
def firstPart (p : EuclideanSpace ℝ (Fin k ⊕ Fin m)) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun i => p (Sum.inl i))
theorem pairPt_add (u u' : EuclideanSpace ℝ (Fin k)) (w w' : EuclideanSpace ℝ (Fin m)) :
    pairPt u w + pairPt u' w' = pairPt (u + u') (w + w') := by
  ext i
  rcases i with i | i <;> simp [pairPt]
theorem pairPt_smul (c : ℝ) (u : EuclideanSpace ℝ (Fin k)) (w : EuclideanSpace ℝ (Fin m)) :
    c • pairPt u w = pairPt (c • u) (c • w) := by
  ext i
  rcases i with i | i <;> simp [pairPt]
def graphLin (A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k ⊕ Fin m) where
  toFun x := pairPt x (A x)
  map_add' x y := by rw [map_add, pairPt_add]
  map_smul' c x := by rw [map_smul, pairPt_smul]; rfl
end AreaGraphPiece
end
end GroundTheory.Heights₂.Heights


