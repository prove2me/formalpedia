-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:23.482956+00:00
-- url     : https://prove2.me/theorems/6f26940f-7bcc-4e17-98ab-d3aa1360ab5e
-- title:
--   Field Change
-- statement:
--   Definitions and structural lemmas for Field Change, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/FieldChange.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CardEmbeddingsRestrict
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
open NumberField Module
noncomputable section
section Extension
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
end Extension
section Cone
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
end Cone
end
end GroundTheory.Heights₂.Heights


