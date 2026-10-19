-- Prove2me | Definitions.Def_MazurTransfer_Order13ReciprocalEmbeddingOverlapCertificate
-- name    : MazurTransfer_Order13ReciprocalEmbeddingOverlapCertificate
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T13:28:44.234684+00:00
-- url     : https://prove2.me/theorems/b6d90238-e700-41c6-a12d-7d4150897453
-- title:
--   The actual reciprocal coordinate embedding agrees with its overlap restriction
-- statement:
--   Over a characteristic-zero field, the original coordinate embedding of the reciprocal ring into the actual curve function field equals localization into the reciprocal overlap ring followed by its specified embedding. This exact commutation certificate is used in the original Pell coordinate-transition identities.
-- source:
--   Original complete reciprocal_embedding_overlap declaration and proof from MazurTheorem Order13ChartOverlapFunctionField.lean, Apache-2.0, Vas and contributors. Its full original closed type is kernel-compared. Public original overlap data and the proved general affine restriction theorem supply dependencies. Named downstream consumer: original Pell chart-overlap identities.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the literal gluing transition identifies the two affine
coordinate embeddings in the actual scheme function field. Named downstream
consumer: the ordinary-chart expression for the Pell function.
-/
import Definitions.Def_MazurTransfer_Order13ChartOverlapEmbeddingData
import Theorems.Thm_MazurTransfer_AffineOpenChartFunctionFieldNaturality_coordinate_embedding_restriction
noncomputable section
universe u
open MazurTransfer
namespace MazurTransfer.Order13ChartOverlapFunctionField
open AlgebraicGeometry CategoryTheory
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTorsion.XOneThirteenAffineCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open AffineOpenChartFunctionField AffineOpenChartFunctionFieldNaturality
variable (K : Type u) [Field K] [CharZero K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩

theorem reciprocal_embedding_overlap (b : ReciprocalRing K) :
    algebraMap (ReciprocalRing K) (actualCurveFunctionField K) b =
      overlapEmbedding K (algebraMap (ReciprocalRing K) (ReciprocalOverlapRing K) b) :=
  congrArg (fun f => f.hom b)
    (coordinate_embedding_restriction (.of (ReciprocalRing K)) (reciprocalChartMap K)
      (.of (ReciprocalOverlapRing K))
      (CommRingCat.ofHom (algebraMap (ReciprocalRing K) (ReciprocalOverlapRing K))))

end MazurTransfer.Order13ChartOverlapFunctionField
#print axioms MazurTransfer.Order13ChartOverlapFunctionField.reciprocal_embedding_overlap


