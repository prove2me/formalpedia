-- Prove2me | Definitions.Def_Kyprianou_Ch01_PassageZeroBoundaryCertificatesV2
-- name    : Kyprianou_Ch01_PassageZeroBoundaryCertificatesV2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-16T23:30:02.285923+00:00
-- url     : https://prove2.me/theorems/a67d8ae1-246c-49be-8a9e-56f714986fe4
-- title:
--   Source-faithful Chapter 1 Brownian passage certificates with pathwise zero-level boundary

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ChapterCertification
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal Classical
set_option autoImplicit false
namespace Kyprianou.Ch01

/-- Corrected source-faithful pathwise level-zero Brownian passage obligation. -/
noncomputable def certificate_inverseGaussianPassageLevySubordinatorZeroBoundaryV2 : Prop :=
∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (b : ℝ) (hb : 0 < b)
    (hB : Kyprianou.Ch01.IsLinearBrownian P X 1 b)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω)) ,
    let T : ℝ≥0 → Ω → ℝ :=
      fun s ω =>
        if s = 0 then (0 : ℝ)
        else (match Kyprianou.Ch01.firstUpperPassage X (s : ℝ) ω with
        | none => (0 : ℝ)
        | some t => (t : ℝ))
    (∀ s : ℝ≥0, 0 < s →
      ∀ᵐ ω ∂P,
        Kyprianou.Ch01.firstUpperPassage X (s : ℝ) ω ≠ ⊤) ∧
      ProbabilityTheory.IsLevyProcess T P ∧
      (∀ (s : ℝ≥0) (q : ℝ), 0 < s → 0 ≤ q →
        Integrable (fun ω => Real.exp (-q * T s ω)) P ∧
        (∫ ω, Real.exp (-q * T s ω) ∂P) =
          Real.exp (-(s : ℝ) *
            (Real.sqrt (b ^ 2 + 2 * q) - b)))

/-- Corrected source-faithful pathwise level-zero Brownian passage obligation. -/
noncomputable def certificate_brownianPassageHalfStableLevyProcessZeroBoundaryV2 : Prop :=
∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ)
    (hB : Kyprianou.Ch01.IsLinearBrownian P B 1 0)
    (hMeas : ∀ t : ℝ≥0, Measurable (B t))
    (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => B t ω)) ,
    let T : ℝ≥0 → Ω → ℝ :=
      fun s ω =>
        if s = 0 then (0 : ℝ)
        else (match Kyprianou.Ch01.firstUpperPassage B (s : ℝ) ω with
        | none => (0 : ℝ)
        | some t => (t : ℝ))
    (∀ s : ℝ≥0, 0 < s →
      ∀ᵐ ω ∂P,
        Kyprianou.Ch01.firstUpperPassage B (s : ℝ) ω ≠ ⊤) ∧
    ProbabilityTheory.IsLevyProcess T P ∧
    (∀ (s : ℝ≥0) (q : ℝ), 0 < s → 0 ≤ q →
      Integrable (fun ω => Real.exp (-q * T s ω)) P ∧
      (∫ ω, Real.exp (-q * T s ω) ∂P) =
        Real.exp (-(s : ℝ) * Real.sqrt (2 * q)))

end Kyprianou.Ch01


