-- Prove2me | Definitions.Def_weightedRootFiniteContourComponentsV2
-- name    : weightedRootFiniteContourComponentsV2
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-09-16T15:14:04.760961+00:00
-- url     : https://prove2.me/theorems/e412f6cc-77b1-4f14-ae4d-c1eaa9eb9aad
-- title:
--   Finite weighted-root keyhole contour components (corrected)
-- statement:
--   Concrete finite-height bank, vertical-side, and circular-arc integrals for the weighted-root keyhole contour, together with canonical truncation parameters ε_m = 1/(m+1) and H_m = m+1.
-- source:
--   Parametrized finite keyhole contour associated with the weighted-root integrand.

import Mathlib
import Definitions.Def_weightedRootKeyholeIntegrand
import Definitions.Def_weightedRootComponentIntegrals
import Definitions.Def_keyholeLineIntegral
open scoped BigOperators Interval

noncomputable def weightedRootFiniteUpperBankIntegral (n : ℕ) (a w : ℕ → ℝ) (a₀ a₁ ε : ℝ) : ℂ :=
  keyholeLineIntegral (weightedRootKeyholeIntegrand n a w) (fun t => ((a₀ + t * (a₁ - a₀) : ℝ) : ℂ) + (ε : ℂ) * Complex.I) 0 1
noncomputable def weightedRootFiniteLowerBankIntegral (n : ℕ) (a w : ℕ → ℝ) (a₀ a₁ ε : ℝ) : ℂ :=
  keyholeLineIntegral (weightedRootKeyholeIntegrand n a w) (fun t => ((a₁ + t * (a₀ - a₁) : ℝ) : ℂ) - (ε : ℂ) * Complex.I) 0 1
noncomputable def weightedRootRightVerticalIntegral (n : ℕ) (a w : ℕ → ℝ) (a₁ ε H : ℝ) : ℂ :=
  keyholeLineIntegral (weightedRootKeyholeIntegrand n a w) (fun t => (a₁ : ℂ) + ((ε + t * (H - ε) : ℝ) : ℂ) * Complex.I) 0 1
noncomputable def weightedRootLeftVerticalIntegral (n : ℕ) (a w : ℕ → ℝ) (a₀ ε H : ℝ) : ℂ :=
  keyholeLineIntegral (weightedRootKeyholeIntegrand n a w) (fun t => (a₀ : ℂ) + ((ε + t * (H - ε) : ℝ) : ℂ) * Complex.I) 0 1
noncomputable def weightedRootFiniteInnerArcIntegral (n : ℕ) (a w : ℕ → ℝ) (r : ℝ) : ℂ := weightedRootInnerArcIntegral n a w r
noncomputable def weightedRootFiniteOuterArcIntegral (n : ℕ) (a w : ℕ → ℝ) (R : ℝ) : ℂ := weightedRootOuterArcIntegral n a w R
noncomputable def weightedRootTruncationEpsilon (m : ℕ) : ℝ := 1 / (m + 1 : ℝ)
noncomputable def weightedRootTruncationHeight (m : ℕ) : ℝ := m + 1


