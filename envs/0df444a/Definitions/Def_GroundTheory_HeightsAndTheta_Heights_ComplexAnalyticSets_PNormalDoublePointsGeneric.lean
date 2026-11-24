-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalDoublePointsGeneric
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalDoublePointsGeneric
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:17.43435+00:00
-- url     : https://prove2.me/theorems/190b409f-84ca-4035-9d81-7c12cb4a5c3a
-- title:
--   PNormal Double Points Generic
-- statement:
--   Definitions and structural lemmas for PNormal Double Points Generic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalDoublePointsGeneric.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalDoublePointsGeneric
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
open MvPolynomial Topology ComplexSets
noncomputable section
namespace NormalDoublePointsGeneric
def belowNat : ℕ → WithBot ℕ∞
  | 0 => ⊥
  | e + 1 => (e : WithBot ℕ∞)
end NormalDoublePointsGeneric
end
end GroundTheory.Heights₂.Heights


