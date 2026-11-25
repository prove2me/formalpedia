-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsLineIndex
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsLineIndex
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T02:59:33.487805+00:00
-- url     : https://prove2.me/theorems/dbe3e5a3-5065-4934-a016-f43d27dd9631
-- title:
--   Statements Line Index
-- statement:
--   Definitions and structural lemmas for Statements Line Index, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StatementsLineIndex.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsVectorOrbits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField
noncomputable section
def LineIndexNeZero.Statement (E W : Type*) [Field E] [NumberField E] [AddCommGroup W] [Module E W] :
    Prop :=
  ∀ (La : AddSubgroup W) (x : W), IsLattice E La → x ∈ La → x ≠ 0 → lineIndex E La x ≠ 0
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


