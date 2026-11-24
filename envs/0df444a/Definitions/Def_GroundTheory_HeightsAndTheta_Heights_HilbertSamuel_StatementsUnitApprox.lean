-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsUnitApprox
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsUnitApprox
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:53.648185+00:00
-- url     : https://prove2.me/theorems/4a9d2fa6-d866-45ed-92cb-12b37ba55ad4
-- title:
--   Statements Unit Approx
-- statement:
--   Definitions and structural lemmas for Statements Unit Approx, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsUnitApprox.lean

import Mathlib
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
open NumberField
def UnitApprox.Statement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (u : (F →+* ℂ) → ℝ),
    (∀ sg, u (ComplexEmbedding.conjugate sg) = u sg) → ∑ sg, u sg = 0 →
    ∃ C : ℝ, ∀ n : ℕ, ∃ ε : (𝓞 F)ˣ, ∀ sg : F →+* ℂ,
      |Real.log ‖sg ((ε : 𝓞 F) : F)‖ - n * u sg| ≤ C
end GroundTheory.Heights₂.Heights.HilbertSamuel


