-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGenericSections
-- name    : GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGenericSections
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:19:52.352228+00:00
-- url     : https://prove2.me/theorems/89f5517b-b0e4-446c-a82c-afe290721376
-- title:
--   Statements Generic Sections
-- statement:
--   Definitions and structural lemmas for Statements Generic Sections, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/StatementsGenericSections.lean

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
open CategoryTheory AlgebraicGeometry
noncomputable section
def GenericSectionsInj.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f],
    ∃ m : ℕ, 0 < m ∧ ∀ (k : ℤ) (hk : IsUnit (k : ℚ)), (m : ℤ) ∣ k →
      ∀ W : (invOpen f k : Scheme.{0}).Opens, Function.Injective ((toInvOpen f ℚ k hk).app W)
end
end GroundTheory.Heights₂.Heights.Model


