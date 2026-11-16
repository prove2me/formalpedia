-- Prove2me | Definitions.Def_Kyprianou_Ch01_Exercise110FullCertificates
-- name    : Kyprianou_Ch01_Exercise110FullCertificates
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T10:38:10.695273+00:00
-- url     : https://prove2.me/theorems/b77848ad-3567-4eeb-b200-474f6402f037
-- title:
--   Chapter 1 exercise 1.10 full Brownian martingale and upward passage certificates
-- statement:
--   Full quantified source propositions for Exercise 1.10(i) and the upward first-passage identity of Exercise 1.10(ii). Both are mandatory independent proof obligations.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.10(i)–(ii), printed page 32.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false
universe u
namespace Kyprianou.Ch01

/-! Exact source proposition for Kyprianou.Ch01.brownianRealExponentialMartingale. -/
noncomputable def certificate_brownianRealExponentialMartingale : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma theta : ℝ)
    (hsigma : 0 < sigma)
    (hX : IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t)),
let psi : ℝ := sigma ^ 2 * theta ^ 2 / 2 + gamma * theta
    let M : ℝ≥0 → Ω → ℝ :=
      fun t ω => Real.exp (theta * X t ω - psi * (t : ℝ))
    ∀ (s t : ℝ≥0), s ≤ t →
      Integrable (M t) P ∧
      ∀ A : Set Ω,
        @MeasurableSet Ω (naturalSigma X s) A →
        (∫ ω in A, M t ω ∂P) = (∫ ω in A, M s ω ∂P)

/-! Exact source proposition for Kyprianou.Ch01.brownianDiscountedUpperPassage. -/
noncomputable def certificate_brownianDiscountedUpperPassage : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma q x : ℝ)
    (hsigma : 0 < sigma) (hq : 0 < q) (hx : 0 < x)
    (hX : IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t)),
Integrable (passageLaplace (firstUpperPassage X x) q) P ∧
    (∫ ω, passageLaplace (firstUpperPassage X x) q ω ∂P) =
      Real.exp (-x * ((Real.sqrt
        (gamma ^ 2 + 2 * sigma ^ 2 * q) - gamma) / sigma ^ 2))

end Kyprianou.Ch01


