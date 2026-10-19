-- Prove2me | Definitions.Def_MazurTransfer_Order13ChartOverlapEmbeddingData
-- name    : MazurTransfer_Order13ChartOverlapEmbeddingData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T13:20:45.825805+00:00
-- url     : https://prove2.me/theorems/7c9483d1-5755-49b3-ab61-2ddddf2751e7
-- title:
--   The actual reciprocal overlap embedding into the existing scheme function field
-- statement:
--   For every field $K$ of characteristic zero, the original ordinary-to-reciprocal overlap map is an open immersion, the reciprocal overlap ring is a domain, and it embeds into the literal curve function field. These are the original coordinate and localization constructors used to compare the Pell function on the two affine charts.
-- source:
--   Original complete six declarations ordinaryToReciprocalBase_spec_map, reciprocalOverlapRing_isDomain, reciprocalOverlapInclusion_isOpenImmersion, ordinaryOverlapInclusion_isOpenImmersion, ordinaryToReciprocalBase_isOpenImmersion and overlapEmbedding from MazurTheorem Order13ChartOverlapFunctionField.lean, Apache-2.0, Vas and contributors. Six complete original types and one data value are kernel-compared. Public imports provide the original ordinary and reciprocal field structures. Named downstream consumer: actual Pell chart-overlap equality.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the literal gluing transition identifies the two affine
coordinate embeddings in the actual scheme function field. Named downstream
consumer: the ordinary-chart expression for the Pell function.
-/
import Definitions.Def_MazurTransfer_Order13ActualOrdinaryFunctionFieldCoordinates
import Definitions.Def_MazurTransfer_Order13ReciprocalChartActualFunctionField
noncomputable section
universe u
namespace MazurTransfer.Order13ChartOverlapFunctionField
open AlgebraicGeometry CategoryTheory
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTorsion.XOneThirteenAffineCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open AffineOpenChartFunctionField
variable (K : Type u) [Field K] [CharZero K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩

omit [CharZero K] in
theorem ordinaryToReciprocalBase_spec_map :
    Spec.map (CommRingCat.ofHom (ordinaryToReciprocalBase K).toRingHom) =
      (overlapSchemeIso K).inv ≫
        Spec.map (CommRingCat.ofHom (algebraMap (CoordinateRing K) (OrdinaryOverlapRing K))) := by
  rw [overlapSchemeIso_inv, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro b
  exact (ordinaryToReciprocal_algebraMap K b).symm

instance reciprocalOverlapRing_isDomain : IsDomain (ReciprocalOverlapRing K) :=
  Localization.Away.isDomain (Order13SingleSectionFiniteAlgebra.actual_reciprocal_z_ne_zero K)

instance reciprocalOverlapInclusion_isOpenImmersion :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (ReciprocalRing K) (ReciprocalOverlapRing K)))) :=
  IsOpenImmersion.of_isLocalization (zCoordinate K)

instance ordinaryOverlapInclusion_isOpenImmersion :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (CoordinateRing K) (OrdinaryOverlapRing K)))) :=
  IsOpenImmersion.of_isLocalization (xCoordinate K)

instance ordinaryToReciprocalBase_isOpenImmersion :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (ordinaryToReciprocalBase K).toRingHom)) := by
  rw [ordinaryToReciprocalBase_spec_map]
  infer_instance

def overlapEmbedding : ReciprocalOverlapRing K →+* actualCurveFunctionField K :=
  coordinateEmbedding (.of (ReciprocalOverlapRing K))
    (Spec.map (CommRingCat.ofHom (algebraMap (ReciprocalRing K) (ReciprocalOverlapRing K))) ≫
      reciprocalChartMap K)

end MazurTransfer.Order13ChartOverlapFunctionField
#print axioms MazurTransfer.Order13ChartOverlapFunctionField.ordinaryToReciprocalBase_spec_map
#print axioms MazurTransfer.Order13ChartOverlapFunctionField.reciprocalOverlapRing_isDomain
#print axioms MazurTransfer.Order13ChartOverlapFunctionField.reciprocalOverlapInclusion_isOpenImmersion
#print axioms MazurTransfer.Order13ChartOverlapFunctionField.ordinaryOverlapInclusion_isOpenImmersion
#print axioms MazurTransfer.Order13ChartOverlapFunctionField.ordinaryToReciprocalBase_isOpenImmersion
#print axioms MazurTransfer.Order13ChartOverlapFunctionField.overlapEmbedding


