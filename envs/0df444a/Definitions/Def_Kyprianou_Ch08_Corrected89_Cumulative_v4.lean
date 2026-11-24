-- Prove2me | Definitions.Def_Kyprianou_Ch08_Corrected89_Cumulative_v4
-- name    : Kyprianou_Ch08_Corrected89_Cumulative_v4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T12:51:03.945409+00:00
-- url     : https://prove2.me/theorems/9062e4a8-3f5e-4fec-9bd7-a3dfdbeee8f2
-- title:
--   Corrected Chapter 8 cumulative source certificate with Theorem 8.9 v3
-- statement:
--   All 24 Chapter 8 source obligations, with only Theorem 8.9 corrected to destination minus origin.
-- source:
--   Kyprianou (2006), Chapter 8; corrected Theorem 8.9 record 187462f1-7ddf-402e-8f78-fa61aba5d226.

import Definitions.Def_Kyprianou_Ch08_OriginDriftSign_v3
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- Source-corrected Theorem 8.9 certificate: destination minus origin. -/
def sourceCertificate_result8_9_v3 : Prop :=
  ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ (q x : ℝ), 0 < q →
      DifferentiableAt ℝ (Phi ψ) q ∧
      ∃ U : Measure ℝ,
        IsResolvent P (shifted D.X x) q U ∧
        U = volume.withDensity
          (fun y : ℝ =>
            ENNReal.ofReal
              (unrestrictedPotentialDensity ψ q (W q) (y - x)))

/-- Corrected Chapter 8 cumulative source certificate. -/
def sourceCertificate_chapterEightMain_v4 : Prop :=
  sourceCertificate_result8_1 ∧
  sourceCertificate_result8_2 ∧
  sourceCertificate_result8_3 ∧
  sourceCertificate_result8_4 ∧
  sourceCertificate_result8_5 ∧
  sourceCertificate_result8_6_v3 ∧
  sourceCertificate_result8_7 ∧
  sourceCertificate_result8_8 ∧
  sourceCertificate_result8_9_v3 ∧
  sourceCertificate_result8_10 ∧
  sourceCertificate_result8_11 ∧
  sourceCertificate_result8_12 ∧
  sourceCertificate_exercise8_1 ∧
  sourceCertificate_exercise8_2 ∧
  sourceCertificate_exercise8_3 ∧
  sourceCertificate_exercise8_4 ∧
  sourceCertificate_exercise8_5 ∧
  sourceCertificate_exercise8_6 ∧
  sourceCertificate_exercise8_7 ∧
  sourceCertificate_exercise8_8 ∧
  sourceCertificate_exercise8_9 ∧
  sourceCertificate_exercise8_10 ∧
  sourceCertificate_exercise8_11 ∧
  sourceCertificate_exercise8_12

end Kyprianou.Ch08.StageB


