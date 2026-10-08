-- Prove2me | Definitions.Def_weightedRootComponentIntegrals
-- name    : weightedRootComponentIntegrals
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-09-16T13:15:28.489688+00:00
-- url     : https://prove2.me/theorems/dc9e56a0-2db7-40e2-8e7a-3830f3e2879b
-- title:
--   Weighted-root keyhole component integrals
-- statement:
--   We define the four oriented component line integrals of the weighted-root keyhole integrand along the upper bank, lower bank, inner circular arc, and outer circular arc.
-- source:
--   Component decomposition of the standard weighted-root keyhole contour.

import Mathlib
import Definitions.Def_weightedRootKeyholeIntegrand
import Definitions.Def_keyholeLineIntegral
open scoped BigOperators Interval

noncomputable def weightedRootUpperBankIntegral (n : ℕ) (a w : ℕ → ℝ) (a₀ a₁ : ℝ) : ℂ :=
  keyholeUpperBankIntegral (weightedRootKeyholeIntegrand n a w) a₀ a₁

noncomputable def weightedRootLowerBankIntegral (n : ℕ) (a w : ℕ → ℝ) (a₀ a₁ : ℝ) : ℂ :=
  keyholeLowerBankIntegral (weightedRootKeyholeIntegrand n a w) a₀ a₁

noncomputable def weightedRootInnerArcIntegral (n : ℕ) (a w : ℕ → ℝ) (r : ℝ) : ℂ :=
  keyholeInnerArcIntegral (weightedRootKeyholeIntegrand n a w) r

noncomputable def weightedRootOuterArcIntegral (n : ℕ) (a w : ℕ → ℝ) (R : ℝ) : ℂ :=
  keyholeOuterArcIntegral (weightedRootKeyholeIntegrand n a w) R


