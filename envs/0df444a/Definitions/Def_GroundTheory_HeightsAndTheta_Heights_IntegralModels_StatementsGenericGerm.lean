-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGenericGerm
-- name    : GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGenericGerm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:38.537622+00:00
-- url     : https://prove2.me/theorems/a31b4534-e1e9-482b-af49-ec7c6ba3ab58
-- title:
--   Statements Generic Germ
-- statement:
--   Definitions and structural lemmas for Statements Generic Germ, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/StatementsGenericGerm.lean

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
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
def GenericGermInjective.Statement : Prop :=
  ∀ (X : Scheme.{0}) [IsIntegral X] (E : X.Modules), IsVectorBundle E →
    ∀ (U : X.Opens) (hU : genericPoint X ∈ U),
      Function.Injective (E.presheaf.germ U (genericPoint X) hU)
end GroundTheory.Heights₂.Heights.Model


