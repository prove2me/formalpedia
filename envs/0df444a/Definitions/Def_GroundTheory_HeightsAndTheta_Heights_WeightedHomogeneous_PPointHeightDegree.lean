-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PPointHeightDegree
-- name    : GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PPointHeightDegree
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T18:08:17.080237+00:00
-- url     : https://prove2.me/theorems/720f6b3c-7f84-4e51-9401-3c1fa67dfeb3
-- title:
--   PPoint Height Degree
-- statement:
--   Definitions and structural lemmas for PPoint Height Degree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PPointHeightDegree.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsPointHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
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
open NumberField Module Matrix
open scoped ComplexOrder
noncomputable section
section Embedding
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
end Embedding
end
end GroundTheory.Heights₂.Heights


