-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietyMassLower
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietyMassLower
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:49.896889+00:00
-- url     : https://prove2.me/theorems/6e3a2535-d5df-46dc-a02b-a3049ca6c482
-- title:
--   St Variety Mass Lower
-- statement:
--   Definitions and structural lemmas for St Variety Mass Lower, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StVarietyMassLower.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory ComplexSets
noncomputable section
def VarietyMassLower.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → ∀ R : ℝ,
      ∃ c : ℝ, 0 < c ∧ ∀ z ∈ zeroSetEuc J, ‖z‖ ≤ R → ∀ ρ ∈ Set.Ioc (0 : ℝ) 1,
        ENNReal.ofReal (c * ρ ^ (2 * d)) ≤
          μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball z ρ)
end
end GroundTheory.Heights₂.Heights


