-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualInfinityValuationData
-- name    : MazurTransfer_Order13ActualInfinityValuationData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T12:10:37.181798+00:00
-- url     : https://prove2.me/theorems/7b100b0f-e381-4e61-a735-f2da9ac611e4
-- title:
--   Actual infinity places, raw valuations and the normalized Pell function
-- statement:
--   The two actual reciprocal-chart localizations at $(z,w)=(0,a)$, with $a^2=1$ over $\mathbb Q$, define places of the existing literal scheme function field. Their original raw valuations and order formulas give $$\operatorname{ord}_{v_a}(z)=1,\qquad \operatorname{ord}_{v_a}(u)=0\quad(u\text{ a local unit}).$$ The specified normalized Pell function is $P_{\infty,+}/z^{19}$. These exact original objects and certificates supply its infinity orders and principal divisor.
-- source:
--   Original complete eight declarations selected from MazurTheorem Order13PellActualInfinityValuations.lean, Apache-2.0, Vas and contributors. Eight complete original closed types and three data values are kernel-compared. Original generated local Fact instances are expanded only from their retained checked values, including the separately checked reciprocal-embedding dependency. All original bodies are unchanged; explicit local DVR instances consume the Proved original DVR theorem. Named downstream consumer: actual Pell infinity orders and principal divisor. The original Proved maximal-ideal theorem is an explicit public import; no declaration statement or body changes.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the two actual reciprocal localizations define genuine
places of the literal rational scheme function field, and z has order one.
Named downstream consumer: the Pell principal-divisor formula on that field.
The identification with the two infinity section centers is separate work.
-/
import Definitions.Def_MazurTransfer_Order13ReciprocalChartActualFunctionField
import Definitions.Def_MazurTransfer_Order13PellCoordinateFactors
import Theorems.Thm_MazurTransfer_Order13InfinityDiscreteValuationRing_localRing_isDiscreteValuationRing
import Theorems.Thm_MazurTransfer_Order13InfinityLocalParameter_maximalIdeal_eq_span_z
import Theorems.Thm_AlgebraicCurve_Place_ord_eq_neg_log_of_valuationSubring_eq
noncomputable section
namespace MazurTransfer.Order13PellActualInfinityValuations
open AlgebraicGeometry AlgebraicCurve IsDedekindDomain WithZero
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13InfinityLocalParameter Order13ReciprocalChartActualFunctionField
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance (a : ℚ) (ha : a ^ 2 = 1) : IsDiscreteValuationRing (LocalRing ℚ a ha) :=
  Order13InfinityDiscreteValuationRing.localRing_isDiscreteValuationRing ℚ a ha

def infinityPlace (a : ℚ) (ha : a ^ 2 = 1) : Place ℚ (actualCurveFunctionField ℚ) :=
  Place.ofHeightOneSpectrum (IsDiscreteValuationRing.maximalIdeal (LocalRing ℚ a ha))

def rawValuation (a : ℚ) (ha : a ^ 2 = 1) : Valuation (actualCurveFunctionField ℚ) ℤᵐ⁰ :=
  (IsDiscreteValuationRing.maximalIdeal (LocalRing ℚ a ha)).valuation (actualCurveFunctionField ℚ)

theorem rawValuation_z (a : ℚ) (ha : a ^ 2 = 1) :
    rawValuation a ha (algebraMap (LocalRing ℚ a ha) (actualCurveFunctionField ℚ) (z ℚ a ha)) =
      exp (-1 : ℤ) := by
  rw [rawValuation, HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_singleton _
    (Order13InfinityDiscreteValuationRing.z_ne_zero ℚ a ha)
    (Order13InfinityLocalParameter.maximalIdeal_eq_span_z ℚ a ha (by norm_num))

theorem rawValuation_isUnit (a : ℚ) (ha : a ^ 2 = 1)
    (b : LocalRing ℚ a ha) (hb : IsUnit b) :
    rawValuation a ha (algebraMap (LocalRing ℚ a ha) (actualCurveFunctionField ℚ) b) = 1 := by
  rw [rawValuation, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_one_iff]
  change b ∉ IsLocalRing.maximalIdeal (LocalRing ℚ a ha)
  simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] using hb

theorem ord_algebraMap (a : ℚ) (ha : a ^ 2 = 1)
    (b : LocalRing ℚ a ha) (hb : b ≠ 0) :
    (infinityPlace a ha).ord (algebraMap (LocalRing ℚ a ha) (actualCurveFunctionField ℚ) b) =
      -log (rawValuation a ha (algebraMap (LocalRing ℚ a ha) (actualCurveFunctionField ℚ) b)) :=
  Place.ord_eq_neg_log_of_valuationSubring_eq (infinityPlace a ha) (rawValuation a ha) rfl
    (rawValuation_z a ha) ((map_ne_zero_iff _
      (IsFractionRing.injective (LocalRing ℚ a ha) (actualCurveFunctionField ℚ))).mpr hb)

theorem infinityPlace_ord_z (a : ℚ) (ha : a ^ 2 = 1) :
    (infinityPlace a ha).ord (algebraMap (ReciprocalRing ℚ) (actualCurveFunctionField ℚ)
      (zCoordinate ℚ)) = 1 := by
  rw [← localEmbedding_coordinate ℚ a ha (zCoordinate ℚ)]
  change (infinityPlace a ha).ord (algebraMap (LocalRing ℚ a ha) (actualCurveFunctionField ℚ)
    (z ℚ a ha)) = 1
  rw [ord_algebraMap a ha _ (Order13InfinityDiscreteValuationRing.z_ne_zero ℚ a ha),
    rawValuation_z, log_exp]
  norm_num

theorem infinityPlace_ord_isUnit (a : ℚ) (ha : a ^ 2 = 1)
    (b : LocalRing ℚ a ha) (hb : IsUnit b) :
    (infinityPlace a ha).ord (algebraMap (LocalRing ℚ a ha) (actualCurveFunctionField ℚ) b) = 0 := by
  rw [ord_algebraMap a ha b hb.ne_zero, rawValuation_isUnit a ha b hb, log_one, neg_zero]

def pellFunction : actualCurveFunctionField ℚ :=
  algebraMap (ReciprocalRing ℚ) (actualCurveFunctionField ℚ)
    (Order13PellChartCertificate.reciprocalPlus ℚ) /
      algebraMap (ReciprocalRing ℚ) (actualCurveFunctionField ℚ) (zCoordinate ℚ) ^ 19

end MazurTransfer.Order13PellActualInfinityValuations
#print axioms MazurTransfer.Order13PellActualInfinityValuations.infinityPlace
#print axioms MazurTransfer.Order13PellActualInfinityValuations.infinityPlace_ord_z
#print axioms MazurTransfer.Order13PellActualInfinityValuations.pellFunction


