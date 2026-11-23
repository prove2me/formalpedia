-- Prove2me | Definitions.Def_Kyprianou_Ch08_OriginDriftSign_v3
-- name    : Kyprianou_Ch08_OriginDriftSign_v3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-23T17:18:31.074676+00:00
-- url     : https://prove2.me/theorems/2e4ae4d0-278f-460e-b128-a6fcefb292ed
-- title:
--   Corrected Lemma 8.6 source certificate and BV drift sign
-- statement:
--   The model triplet drift b enters bvDrift as -b; versioned faithful correction while preserving the old certificate.
-- source:
--   Kyprianou (2006), Lemma 8.6, corrected using the published Kyprianou Chapter 1 positive characteristic exponent and Proved source_result81_law_positive_mgf.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- Source-corrected physical drift argument for Lemma 8.6. -/
def sourceCertificate_result8_6_v3 : Prop :=
∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ q : ℝ, 0 ≤ q →
        ((W q 0 = 0) ↔
          ¬ HasBoundedVariationTriplet
              D.gaussianCoefficient D.triplet.levyMeasure) ∧
        (HasBoundedVariationTriplet
          D.gaussianCoefficient D.triplet.levyMeasure →
          0 < bvDrift (-D.triplet.drift) D.triplet.levyMeasure ∧
          W q 0 = (bvDrift (-D.triplet.drift) D.triplet.levyMeasure)⁻¹)

/-- Versioned origin value predicate. -/
def result8_6_v3 : Prop := sourceCertificate_result8_6_v3

end Kyprianou.Ch08.StageB


