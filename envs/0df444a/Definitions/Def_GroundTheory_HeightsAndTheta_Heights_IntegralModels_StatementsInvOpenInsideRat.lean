-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsInvOpenInsideRat
-- name    : GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsInvOpenInsideRat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:23:27.263859+00:00
-- url     : https://prove2.me/theorems/fdd4c1b1-c894-4d04-a10b-b5db0eabcae1
-- title:
--   Statements Inv Open Inside Rat
-- statement:
--   Definitions and structural lemmas for Statements Inv Open Inside Rat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/StatementsInvOpenInsideRat.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
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
def InvOpenInsideRat.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (W : X.Opens),
    Set.range (baseChangeMap f ℚ) ⊆ Set.range W.ι →
    ∃ m : ℕ, 0 < m ∧ invOpen f m ≤ W
end
end GroundTheory.Heights₂.Heights.Model


