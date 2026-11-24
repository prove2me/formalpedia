-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopCellsOfParts
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_TopCellsOfParts
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T14:50:52.452316+00:00
-- url     : https://prove2.me/theorems/2af98afa-4fce-4d76-96e6-3b3c50918252
-- title:
--   Top Cells Of Parts
-- statement:
--   Definitions and structural lemmas for Top Cells Of Parts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TopCellsOfParts.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
namespace Formalism.FourierDecayAlt.P.Ux13
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
theorem block2_add {p s : ℕ} (A A' : Matrix (Fin p) (Fin p) ℂ) (B B' : Matrix (Fin p) (Fin s) ℂ)
    (C C' : Matrix (Fin s) (Fin p) ℂ) (D D' : Matrix (Fin s) (Fin s) ℂ) :
    blk2 A B C D + blk2 A' B' C' D' = blk2 (A + A') (B + B') (C + C') (D + D') := by
  unfold blk2
  rw [← Matrix.fromBlocks_add]
  ext i j
  simp
theorem smul_block_two {p s : ℕ} (r : ℝ) (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin s) ℂ)
    (C : Matrix (Fin s) (Fin p) ℂ) (D : Matrix (Fin s) (Fin s) ℂ) :
    r • blk2 A B C D = blk2 (r • A) (r • B) (r • C) (r • D) := by
  unfold blk2
  rw [← Matrix.fromBlocks_smul]
  ext i j
  simp
def iotaL (p s : ℕ) : G.Mat s →ₗ[ℝ] G.Mat (p + s) where
  toFun CC := Matrix.of.symm (blk2 (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 (Matrix.of CC))
  map_add' x y := by
    have h : (blk2 (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 (Matrix.of (x + y)) : Matrix (Fin (p + s)) (Fin (p + s)) ℂ) =
        blk2 (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 (Matrix.of x) + blk2 0 0 0 (Matrix.of y) := by
      rw [block2_add]; simp
    exact h
  map_smul' r x := by
    have h : (blk2 (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 (Matrix.of (r • x)) : Matrix (Fin (p + s)) (Fin (p + s)) ℂ) =
        r • blk2 (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 (Matrix.of x) := by
      rw [smul_block_two]; simp
    exact h
def iotaC (p s : ℕ) : G.Mat s →L[ℝ] G.Mat (p + s) := LinearMap.toContinuousLinearMap (iotaL p s)
def gA {p s : ℕ} (T : G.Mat (p + s)) : G.Mat s →ᴬ[ℝ] G.Mat (p + s) where
  toFun x := T + iotaC p s x
  linear := iotaL p s
  map_vadd' x v := by
    show T + iotaL p s (v + x) = iotaL p s v + (T + iotaL p s x)
    rw [map_add]; abel
  cont := continuous_const.add (iotaC p s).continuous
def Lc {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (c : ℂ) : V →L[ℝ] V :=
  (c • ContinuousLinearMap.id ℂ V).restrictScalars ℝ
end Formalism.FourierDecayAlt.P.Ux13


