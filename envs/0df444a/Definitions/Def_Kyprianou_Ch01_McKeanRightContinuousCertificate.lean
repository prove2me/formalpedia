-- Prove2me | Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousCertificate
-- name    : Kyprianou_Ch01_McKeanRightContinuousCertificate
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T08:26:14.848205+00:00
-- url     : https://prove2.me/theorems/d94cfd59-dd6e-43e7-b8f7-d20f847f2e6f
-- title:
--   Sound Chapter 1 McKean certification proposition for right-continuous stopping times
-- statement:
--   Source-faithful replacement for certificate_mckeanBrownianPutOptimal: exactly the original six-conjunct theorem of Kyprianou Chapter 1 Theorem 1.13, retaining all hypotheses, strictly crossing optimal stopping time and smooth fit; both admissibility conjuncts use the right-continuous natural filtration, which is required for hitting open half-lines.
-- source:
--   Kyprianou (2006), Chapter 1 Theorem 1.13; Sousi (2011), Advanced Probability Proposition 3.5.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

universe u
namespace Kyprianou.Ch01
/-- Source obligation: Kyprianou.Ch01.mckeanBrownianPutOptimalRightContinuous. This is a full mathematical proposition, not a proof. -/

noncomputable def certificate_mckeanBrownianPutOptimalRightContinuous : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma K q x : ℝ)
    (hsigma : 0 < sigma) (hK : 0 < K) (hq : 0 < q)
    (hB : IsLinearBrownian P X sigma gamma)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (hAllContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω)),
    let phi : ℝ :=
      (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) + gamma) /
        sigma ^ 2
    let barrier : ℝ := Real.log (K * phi / (1 + phi))
    let tauStar : Ω → WithTop ℝ≥0 :=
      firstLowerPassage X x barrier
    0 < phi ∧
      IsNaturalRightStoppingTime (fun t ω => x + X t ω) tauStar ∧
      Integrable (discountedPut X x K q tauStar) P ∧
      (∫ ω, discountedPut X x K q tauStar ω ∂P) =
        mckeanValue K barrier phi x ∧
      (∀ tau : Ω → WithTop ℝ≥0,
        IsNaturalRightStoppingTime (fun t ω => x + X t ω) tau →
        (∫ ω, discountedPut X x K q tau ω ∂P) ≤
          mckeanValue K barrier phi x) ∧
      HasDerivAt (mckeanValue K barrier phi)
        (-Real.exp barrier) barrier
end Kyprianou.Ch01


