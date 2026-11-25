-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSemilocalFiniteRank
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSemilocalFiniteRank
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T06:19:30.751942+00:00
-- url     : https://prove2.me/theorems/dec9ab13-3174-4bbf-b5f1-a6ab3d88b03e
-- title:
--   PSemilocal Finite Rank
-- statement:
--   Definitions and structural lemmas for PSemilocal Finite Rank, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSemilocalFiniteRank.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsFibreFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocFrac
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
section Rank
variable {F L₀ L : Type*} [Field F] [Field L₀] [Field L] [Algebra F L₀] [Algebra F L]
end Rank
end
end GroundTheory.Heights₂.Heights.FieldNumbers


