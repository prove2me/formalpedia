-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHadamard
-- name    : GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHadamard
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T09:19:41.413674+00:00
-- url     : https://prove2.me/theorems/9b3c9ae0-53f6-5109-a3c2-967ef75ca371
-- title:
--   PHadamard
-- statement:
--   Definitions and structural lemmas for PHadamard, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PHadamard.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
open GroundTheory.Heights₂.Heights InnerProductSpace
universe u v w
noncomputable section
section Gram
variable {K : Type*} [Field K] [NumberField K] {E : Type*} [AddCommGroup E] [Module (𝓞 K) E]
  [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E]
end Gram
end
end GroundTheory.Heights₂.Heights.LatticeLemmas


