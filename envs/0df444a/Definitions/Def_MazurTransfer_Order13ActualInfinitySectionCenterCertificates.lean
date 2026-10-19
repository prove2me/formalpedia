-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualInfinitySectionCenterCertificates
-- name    : MazurTransfer_Order13ActualInfinitySectionCenterCertificates
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T13:12:50.121284+00:00
-- url     : https://prove2.me/theorems/5bbee7af-5d6a-4b5d-801e-44ce02dd98f9
-- title:
--   Actual infinity localization ranges and literal section centers
-- statement:
--   For $a\in\mathbb Q$ with $a^2=1$, the original reciprocal localization embedding has image equal to the valuation subring of its specified infinity place. The closed point of the literal infinity section is exactly its reciprocal chart center. These two certificates identify the localization-defined place with the canonical degree-one section place.
-- source:
--   Original complete localEmbedding_range_eq_place and infinity_section_center statements and proofs from MazurTheorem Order13ActualInfinityPlaceCenters.lean, Apache-2.0, Vas and contributors. The two complete original closed types are kernel-compared. Public imports and an explicit proved local discrete valuation ring instance supply the original dependencies. Named downstream consumer: canonical infinity-place identification.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: identify the two reciprocal-localization places with the
canonical places centered at the two literal rational infinity sections.
Named downstream consumer: the actual degree-19 Pell principal divisor.
The actual stalk diagram supplies the identification, rather than a supplied
valuation equivalence or a substituted abstract curve.
-/
/- Design boundary: the original local valuation-ring range and literal infinity section center.
Named downstream consumer: equality of actual infinity places with canonical section places. -/
import Definitions.Def_MazurTransfer_Order13ActualInfinityPlaceCenterData
import Definitions.Def_MazurTransfer_Order13ActualRationalSectionDegreeOneData
import Definitions.Def_MazurTransfer_Order13IntegralInfinitySections
import Theorems.Thm_MazurTransfer_Order13InfinityDiscreteValuationRing_localRing_isDiscreteValuationRing
noncomputable section
namespace MazurTransfer.Order13ActualInfinityPlaceCenters
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13InfinityLocalParameter Order13ReciprocalChartActualFunctionField
open Order13PellActualInfinityValuations Order13IntegralSections Order13RationalSectionPicardInjection
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance (a : ℚ) (ha : a ^ 2 = 1) : IsDiscreteValuationRing (LocalRing ℚ a ha) :=
  Order13InfinityDiscreteValuationRing.localRing_isDiscreteValuationRing ℚ a ha
theorem localEmbedding_range_eq_place (a : ℚ) (ha : a ^ 2 = 1) :
    (localEmbedding ℚ a ha).range = (infinityPlace a ha).toValuationSubring.toSubring := by
  change (algebraMap (LocalRing ℚ a ha) (actualCurveFunctionField ℚ)).range = _
  rw [RingHom.range_eq_map]
  exact IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring
    (A := LocalRing ℚ a ha) (K := actualCurveFunctionField ℚ)

theorem infinity_section_center (a : ℚ) (ha : a ^ 2 = 1) :
    (sectionClosedPoint ℚ (infinitySection ℚ a ha)).1 = center a ha := by
  change reciprocalChartMap ℚ
    ((Spec.map (CommRingCat.ofHom (reciprocalInfinityEvaluation ℚ a ha)))
      (IsLocalRing.closedPoint ℚ)) = reciprocalChartMap ℚ (chartPoint a ha)
  apply congrArg (reciprocalChartMap ℚ)
  apply PrimeSpectrum.ext
  change Ideal.comap (reciprocalInfinityEvaluation ℚ a ha)
    (IsLocalRing.maximalIdeal ℚ) = RingHom.ker (Order13InfinityEvaluationKernel.evaluation ℚ a ha)
  rw [IsLocalRing.maximalIdeal_eq_bot]
  rfl

end MazurTransfer.Order13ActualInfinityPlaceCenters
#print axioms MazurTransfer.Order13ActualInfinityPlaceCenters.localEmbedding_range_eq_place
#print axioms MazurTransfer.Order13ActualInfinityPlaceCenters.infinity_section_center


