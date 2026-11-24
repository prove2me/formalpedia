-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadStep
-- name    : GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadStep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:24:17.133589+00:00
-- url     : https://prove2.me/theorems/c3ce6904-c885-4843-8b15-0f4382b3f009
-- title:
--   Statements Spread Step
-- statement:
--   Definitions and structural lemmas for Statements Spread Step, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/StatementsSpreadStep.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
def SpreadStep.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (p : Nat.Primes)
    (E : (baseChange f (ZLoc p)).Modules) (W₁ W₂ : X.Opens),
    SpreadsOn f (ZLoc p) E W₁ → SpreadsOn f (ZLoc p) E W₂ →
    ∃ W : X.Opens, baseChangeMap f (ZLoc p) ⁻¹ᵁ W₁ ⊔ baseChangeMap f (ZLoc p) ⁻¹ᵁ W₂ ≤
        baseChangeMap f (ZLoc p) ⁻¹ᵁ W ∧ SpreadsOn f (ZLoc p) E W
end
end GroundTheory.Heights₂.Heights.Model


