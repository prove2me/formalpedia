-- Prove2me | Definitions.Def_MazurTransfer_Order13ReciprocalChartActualFunctionField
-- name    : MazurTransfer_Order13ReciprocalChartActualFunctionField
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T11:54:07.695662+00:00
-- url     : https://prove2.me/theorems/eb467063-9299-4fb7-9030-e684e5de7adb
-- title:
--   The actual reciprocal chart and infinity local rings embed in the existing function field
-- statement:
--   Over every field of characteristic zero, the literal reciprocal coordinate algebra embeds in the existing scheme function field, which is its fraction field. Its localizations at the two infinity evaluation kernels also embed there as fraction-ring bases. The embeddings agree on all reciprocal coordinates: $$A\longrightarrow A_{\mathfrak m_a}\longrightarrow K(C).$$ These are the original chart-induced embeddings and scalar-tower certificates needed to compute the actual Pell divisor.
-- source:
--   Original complete eight declarations from MazurTheorem Order13ReciprocalChartActualFunctionField.lean, Apache-2.0, Vas and contributors. Eight complete original closed types and three data values are kernel-compared. Original module-local Fact instances are expanded only from their retained checked values when their generated names differ. Imports alone are replaced: the actual local-domain data supplies the original domain instances; the unused Pell-order library is not needed here. All original declaration bodies are unchanged. Named downstream consumer: actual Pell infinity valuations and principal divisor.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual reciprocal chart and its infinity localizations
embed in the existing scheme function field, as fraction-ring bases.
Named downstream consumer: the Pell function's actual infinity valuations.
The embeddings come from the literal chart open immersion.
-/
import Definitions.Def_MazurTransfer_AffineOpenChartFunctionField
import Definitions.Def_MazurTransfer_Order13InfinityLocalRingDomain
import Definitions.Def_MazurTransfer_Order13GoodCharacteristicPlaceFoundation

noncomputable section
universe u
namespace MazurTransfer.Order13ReciprocalChartActualFunctionField
open AlgebraicGeometry CategoryTheory
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13InfinityLocalParameter
variable (K : Type u) [Field K] [CharZero K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩

instance reciprocalFunctionFieldAlgebra : Algebra (ReciprocalRing K) (actualCurveFunctionField K) :=
  AffineOpenChartFunctionField.coordinateAlgebra (.of (ReciprocalRing K)) (reciprocalChartMap K)

instance reciprocalFunctionField_isFractionRing :
    IsFractionRing (ReciprocalRing K) (actualCurveFunctionField K) :=
  AffineOpenChartFunctionField.coordinate_isFractionRing (.of (ReciprocalRing K)) (reciprocalChartMap K)

theorem primeCompl_image_isUnit (a : K) (ha : a ^ 2 = 1)
    (b : (infinityIdeal K a ha).primeCompl) :
    IsUnit (algebraMap (ReciprocalRing K) (actualCurveFunctionField K) b) := by
  apply isUnit_iff_ne_zero.mpr
  apply (map_ne_zero_iff _ (IsFractionRing.injective (ReciprocalRing K)
    (actualCurveFunctionField K))).mpr
  intro hb
  apply b.2
  rw [hb]
  exact Ideal.zero_mem _

def localEmbedding (a : K) (ha : a ^ 2 = 1) :
    LocalRing K a ha →+* actualCurveFunctionField K :=
  IsLocalization.lift (S := LocalRing K a ha) (primeCompl_image_isUnit K a ha)

instance localFunctionFieldAlgebra (a : K) (ha : a ^ 2 = 1) :
    Algebra (LocalRing K a ha) (actualCurveFunctionField K) := (localEmbedding K a ha).toAlgebra

theorem localEmbedding_coordinate (a : K) (ha : a ^ 2 = 1) (b : ReciprocalRing K) :
    localEmbedding K a ha (algebraMap (ReciprocalRing K) (LocalRing K a ha) b) =
      algebraMap (ReciprocalRing K) (actualCurveFunctionField K) b :=
  IsLocalization.lift_eq (primeCompl_image_isUnit K a ha) b

instance coordinateLocalFunctionField_isScalarTower (a : K) (ha : a ^ 2 = 1) :
    IsScalarTower (ReciprocalRing K) (LocalRing K a ha) (actualCurveFunctionField K) :=
  IsScalarTower.of_algebraMap_eq fun b => (localEmbedding_coordinate K a ha b).symm

instance localFunctionField_isFractionRing (a : K) (ha : a ^ 2 = 1) :
    IsFractionRing (LocalRing K a ha) (actualCurveFunctionField K) :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (infinityIdeal K a ha).primeCompl (LocalRing K a ha) (actualCurveFunctionField K)

end MazurTransfer.Order13ReciprocalChartActualFunctionField
#print axioms MazurTransfer.Order13ReciprocalChartActualFunctionField.reciprocalFunctionField_isFractionRing
#print axioms MazurTransfer.Order13ReciprocalChartActualFunctionField.localEmbedding_coordinate
#print axioms MazurTransfer.Order13ReciprocalChartActualFunctionField.localFunctionField_isFractionRing


