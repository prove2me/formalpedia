-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_SpreadIsoModelIff
-- name    : GroundTheory_HeightsAndTheta_Heights_IntegralModels_SpreadIsoModelIff
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T04:17:47.226909+00:00
-- url     : https://prove2.me/theorems/d373aeeb-7891-458c-9602-1c699ff90c7f
-- title:
--   Spread Iso Model Iff
-- statement:
--   Definitions and structural lemmas for Spread Iso Model Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/SpreadIsoModelIff.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_invOpen_mul_2a5fb138143a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
open CategoryTheory AlgebraicGeometry
section Along
variable {T T' Y Z : Scheme.{0}} {F G : Z.Modules}
local notation "along" => GroundTheory.Heights₂.Heights.Model.pullbackIsoAlong
end Along
section Facts
variable (X : Scheme.{0})
theorem invOpen_le (a m' : ℕ) : invOpen X (a * m') ≤ invOpen X a := by
  rw [invOpen_mul]; exact inf_le_left
end Facts
section Equiv
local notation "along" => GroundTheory.Heights₂.Heights.Model.pullbackIsoAlong
end Equiv
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model


