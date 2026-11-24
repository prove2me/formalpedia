-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatSheetSumMeasurable
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatSheetSumMeasurable
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:41:56.034341+00:00
-- url     : https://prove2.me/theorems/202d025c-6cd0-44cf-9b71-c20ae7a858fd
-- title:
--   St Rat Sheet Sum Measurable
-- statement:
--   Definitions and structural lemmas for St Rat Sheet Sum Measurable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StRatSheetSumMeasurable.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_RatChartObjects
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory
def RatSheetSumMeasurable.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ)
    (q : MvPolynomial (Fin n) ℂ) (Φ : ℝ → ℝ → ℝ) (g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
    (∀ y, (RatChart.ratFibre J p q y).Finite) → Measurable (Function.uncurry Φ) → Measurable g →
      Measurable fun y => RatChart.ratSheetSum J p q
        (fun x s => Φ (g x) (ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y)) y
end GroundTheory.Heights₂.Heights


