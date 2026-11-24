-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsChartBergman
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsChartBergman
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:58.118348+00:00
-- url     : https://prove2.me/theorems/4b5e67fe-c13f-4770-b5fd-ecea4438a51f
-- title:
--   Statements Chart Bergman
-- statement:
--   Definitions and structural lemmas for Statements Chart Bergman, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsChartBergman.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_BergmanObjects
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm
noncomputable section
def ChartBergmanBound.Statement : Prop :=
  ∀ (D : ℕ) (U : Set (Fin D → ℂ)) (ψ ρ : (Fin D → ℂ) → ℝ) (y₀ : Fin D → ℂ), IsOpen U → y₀ ∈ U →
    ContDiffOn ℝ 2 ψ U → ContinuousOn ρ U → 0 < ρ y₀ → (∀ w, 0 ≤ levi ψ y₀ w) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ F : (Fin D → ℂ) → ℂ, AnalyticOnNhd ℂ F U →
      ENNReal.ofReal (‖F y₀‖ ^ 2 * Real.exp (-(n : ℝ) * ψ y₀)) ≤
        ENNReal.ofReal (((((1 / Real.pi : ℝ) : ℂ) • hessC ψ y₀).det.re / ρ y₀ + ε) *
            (n : ℝ) ^ D) *
          ∫⁻ y in U, ENNReal.ofReal (‖F y‖ ^ 2 * Real.exp (-(n : ℝ) * ψ y) * ρ y)
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


