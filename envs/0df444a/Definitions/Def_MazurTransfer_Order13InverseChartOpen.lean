-- Prove2me | Definitions.Def_MazurTransfer_Order13InverseChartOpen
-- name    : MazurTransfer_Order13InverseChartOpen
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T06:25:51.985636+00:00
-- url     : https://prove2.me/theorems/4355196d-e943-4e0f-8f68-9419b7a3b8db
-- title:
--   The actual inverse chart as the union of the two retained open images
-- statement:
--   Let $R$ be a commutative ring. The ordinary parameter localization and the positive reciprocal patch map to the actual order-thirteen curve by open immersions. Their specified open images determine the literal inverse chart $$V=\operatorname{im}(j_{\mathrm{ord}})\cup\operatorname{im}(j_{\mathrm{rec}}).$$ This is the original chart-open constructor used by the global inverse comparison and integral finite-map data.
-- source:
--   Three original declarations from MazurTheorem Order13InverseParameterAffineOpen.lean, Apache-2.0, Vas and contributors: both original open-immersion instances and inverseChartOpen. All declaration bodies are unchanged; only the import changes to public actual inverse-chart curve maps. All three original closed types and construction values are compared in the kernel. Native, strict and full frontend checks pass with standard axioms only. Named downstream consumers: original finiteModelToCurve_isOpenImmersion, inverse affine-chart isomorphism, and actual integral FiniteMapData.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual inverse finite model is isomorphic to its
literal affine-open image in the original curve.
Named downstream consumer: the second chart of whole single-section
FiniteMapData and the integral Picard representation inputs.
-/
import Definitions.Def_MazurTransfer_Order13InverseFiniteChartCurveMaps

noncomputable section
universe u
namespace MazurTransfer.Order13InverseParameterFiniteAlgebra
open CategoryTheory AlgebraicGeometry
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13SingleSectionFiniteAlgebra (ordinaryParameterLocalization)
variable (R : Type u) [CommRing R]

instance ordinaryParameterCurveMap_isOpenImmersion :
    IsOpenImmersion (ordinaryParameterCurveMap R) := by
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (CoordinateRing R) (ordinaryParameterLocalization R)))) :=
    IsOpenImmersion.of_isLocalization (Order13SingleSectionFiniteMapIdentities.t R)
  unfold ordinaryParameterCurveMap
  infer_instance

instance positiveReciprocalCurveMap_isOpenImmersion :
    IsOpenImmersion (positiveReciprocalCurveMap R) := by
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (ReciprocalRing R) (Order13InverseParameterPositiveReciprocalPatch.PatchRing R)))) :=
    IsOpenImmersion.of_isLocalization (Order13InverseParameterPositiveReciprocalPatch.f R *
      Order13InverseParameterPositiveReciprocalPatch.g R)
  unfold positiveReciprocalCurveMap
  infer_instance

def inverseChartOpen : (curveScheme R).Opens :=
  (ordinaryParameterCurveMap R).opensRange ⊔ (positiveReciprocalCurveMap R).opensRange

variable [IsDomain R] [IsNoetherianRing R]





















end MazurTransfer.Order13InverseParameterFiniteAlgebra



#print axioms MazurTransfer.Order13InverseParameterFiniteAlgebra.inverseChartOpen


