-- Prove2me | Definitions.Def_MazurTransfer_Order13PellChartOverlapIdentities
-- name    : MazurTransfer_Order13PellChartOverlapIdentities
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T13:47:34.537681+00:00
-- url     : https://prove2.me/theorems/9ec6f71a-2006-4b5e-bc1e-1cc1fbc0d482
-- title:
--   Original coordinate images and exact Pell identities on the actual ordinary/reciprocal overlap
-- statement:
--   The specified ordinary and reciprocal coordinates in the existing scheme function field satisfy $xz=1$ and $y=wx^3$. For the original Pell factors, $$H(x)+yK(x)\quad\text{times}\quad z^{19}=H_\infty(z)+wK_\infty(z).$$ The ordinary positive Pell factor over $\mathbb Q$ is a unit. These original certificates supply the equality of the actual infinity-defined Pell function with its ordinary unit expression.
-- source:
--   Original complete eleven selected declarations from MazurTheorem Order13PellActualOrdinaryChart.lean, Apache-2.0, Vas and contributors: zImage, wImage, xImage_overlap, xImage_mul_zImage, yImage_overlap, zImage_ne_zero, xImage_eq_inverse, ordinaryPlus_image, reciprocalPlus_image, ordinaryPlus_mul_zImage and ordinaryPlus_isUnit. Eleven full original types and two data values are kernel-compared. Public original coordinate, overlap and polynomial interfaces supply dependencies. Named downstream consumer: actual ordinary Pell unit expression and zero orders on the ordinary chart.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: identify the actual infinity-defined Pell function with
the ordinary-coordinate unit using the literal chart overlap. Named downstream
consumer: vanishing orders at all places in the ordinary affine chart.
-/
/- Scope: original reciprocal coordinate images and exact Pell chart identities. -/
import Definitions.Def_MazurTransfer_Order13ChartOverlapEmbeddingData
import Definitions.Def_MazurTransfer_Order13ReciprocalEmbeddingOverlapCertificate
import Definitions.Def_MazurTransfer_Order13PellCoordinateFactors
import Theorems.Thm_MazurTransfer_Order13ChartOverlapFunctionField_ordinary_embedding_overlap
import Theorems.Thm_MazurTransfer_Order13PellReciprocalExpression_reciprocal_expression
noncomputable section
universe u
namespace MazurTransfer.Order13PellActualOrdinaryChart
open AlgebraicGeometry CategoryTheory
open MazurTorsion.XOneThirteenProjectiveCurve MazurTorsion.XOneThirteenAffineCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13PellChartCertificate Order13ChartOverlapFunctionField
variable (K : Type u) [Field K] [CharZero K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩

def zImage : actualCurveFunctionField K :=
  algebraMap (ReciprocalRing K) (actualCurveFunctionField K) (zCoordinate K)
def wImage : actualCurveFunctionField K :=
  algebraMap (ReciprocalRing K) (actualCurveFunctionField K) (wCoordinate K)

theorem xImage_overlap : xImage K = overlapEmbedding K (IsLocalization.Away.invSelf (zCoordinate K)) := by
  have H := ordinaryToReciprocalBase_x K
  change ordinaryToReciprocalBase K (xCoordinate K) = IsLocalization.Away.invSelf (zCoordinate K) at H
  exact (ordinary_embedding_overlap K (xCoordinate K)).trans (congrArg (overlapEmbedding K) H)

theorem xImage_mul_zImage : xImage K * zImage K = 1 := by
  have H := congrArg (overlapEmbedding K) (IsLocalization.Away.mul_invSelf
    (S := ReciprocalOverlapRing K) (zCoordinate K))
  rw [xImage_overlap]
  change overlapEmbedding K (IsLocalization.Away.invSelf (zCoordinate K)) *
    algebraMap (ReciprocalRing K) (actualCurveFunctionField K) (zCoordinate K) = 1
  rw [reciprocal_embedding_overlap]
  simpa only [map_mul, map_one, mul_comm] using H

theorem yImage_overlap : yImage K = wImage K * xImage K ^ 3 := by
  have H := ordinaryToReciprocalBase_y K
  change ordinaryToReciprocalBase K (yCoordinate K) =
    algebraMap (ReciprocalRing K) (ReciprocalOverlapRing K) (wCoordinate K) *
      (IsLocalization.Away.invSelf (zCoordinate K)) ^ 3 at H
  change algebraMap (CoordinateRing K) (actualCurveFunctionField K) (yCoordinate K) = _
  rw [ordinary_embedding_overlap, H, map_mul, map_pow, ← reciprocal_embedding_overlap,
    ← xImage_overlap]
  rfl

theorem zImage_ne_zero : zImage K ≠ 0 := by
  intro H
  have H1 := xImage_mul_zImage K
  rw [H, mul_zero] at H1
  exact zero_ne_one H1

theorem xImage_eq_inverse : xImage K = (zImage K)⁻¹ :=
  eq_inv_of_mul_eq_one_left (xImage_mul_zImage K)

theorem ordinaryPlus_image :
    algebraMap (CoordinateRing K) (actualCurveFunctionField K) (ordinaryPlus K) =
      pellH (xImage K) + yImage K * pellK (xImage K) := by
  simp only [ordinaryPlus, pellH, pellK, map_add, map_sub, map_mul, map_pow, map_ofNat]
  rfl

theorem reciprocalPlus_image :
    algebraMap (ReciprocalRing K) (actualCurveFunctionField K) (reciprocalPlus K) =
      infinityPellH (zImage K) + wImage K * infinityPellK (zImage K) := by
  simp only [reciprocalPlus, infinityPellH, infinityPellK, map_add, map_sub, map_mul,
    map_pow, map_ofNat, map_one]
  rfl

theorem ordinaryPlus_mul_zImage :
    algebraMap (CoordinateRing K) (actualCurveFunctionField K) (ordinaryPlus K) * zImage K ^ 19 =
      algebraMap (ReciprocalRing K) (actualCurveFunctionField K) (reciprocalPlus K) := by
  rw [ordinaryPlus_image, reciprocalPlus_image, yImage_overlap, xImage_eq_inverse]
  exact Order13PellReciprocalExpression.reciprocal_expression
    (actualCurveFunctionField K) (zImage K) (wImage K) (zImage_ne_zero K)

theorem ordinaryPlus_isUnit : IsUnit (ordinaryPlus ℚ) :=
  (ordinary_factors_are_units ℚ (isUnit_iff_ne_zero.mpr (by norm_num))).1

end MazurTransfer.Order13PellActualOrdinaryChart
#print axioms MazurTransfer.Order13PellActualOrdinaryChart.zImage
#print axioms MazurTransfer.Order13PellActualOrdinaryChart.wImage
#print axioms MazurTransfer.Order13PellActualOrdinaryChart.xImage_overlap
#print axioms MazurTransfer.Order13PellActualOrdinaryChart.xImage_mul_zImage
#print axioms MazurTransfer.Order13PellActualOrdinaryChart.yImage_overlap
#print axioms MazurTransfer.Order13PellActualOrdinaryChart.zImage_ne_zero
#print axioms MazurTransfer.Order13PellActualOrdinaryChart.xImage_eq_inverse
#print axioms MazurTransfer.Order13PellActualOrdinaryChart.ordinaryPlus_image
#print axioms MazurTransfer.Order13PellActualOrdinaryChart.reciprocalPlus_image
#print axioms MazurTransfer.Order13PellActualOrdinaryChart.ordinaryPlus_mul_zImage
#print axioms MazurTransfer.Order13PellActualOrdinaryChart.ordinaryPlus_isUnit


